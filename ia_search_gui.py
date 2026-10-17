"""
Internet Archive Treasure Finder
---------------------------------
A three-pane Tkinter GUI for digging up the biggest downloadable "nugget"
collections on archive.org for a given search term + media type.

How it works:
  1. Queries archive.org's Advanced Search API (advancedsearch.php) for
     items matching your query + media type filters, sorted by number of
     downloads (a decent proxy for "worth grabbing").
  2. For each candidate item, fetches its metadata record
     (archive.org/metadata/<identifier>) to count real files and total
     size - this is what actually tells you whether an item is a single
     PDF or a 400-file treasure trove.
  3. Lists results in the middle pane, biggest trove first (click any
     column header to re-sort, click again to flip direction).
  4. Selecting a result loads its full file manifest into the right pane,
     where you can filter by file extension (.cbr, .epub, .pdf, ...) and
     jump straight to a direct download link for any file.

No API key needed - these are all public, unauthenticated endpoints.
"""

import threading
import tkinter as tk
import webbrowser
from dataclasses import dataclass, field
from tkinter import ttk, messagebox
from urllib.parse import quote
import queue

import requests

ADVANCED_SEARCH_URL = "https://archive.org/advancedsearch.php"
METADATA_URL = "https://archive.org/metadata/{identifier}"
DETAILS_URL = "https://archive.org/details/{identifier}"
DOWNLOAD_DIR_URL = "https://archive.org/download/{identifier}"

MEDIA_TYPES = [
    ("Images", "image"),
    ("eBooks / Texts", "texts"),
    ("Video", "movies"),
    ("Audio", "audio"),
    ("Software", "software"),
]

USER_AGENT = "ia-treasure-finder/1.0 (personal research tool)"

NOISE_SUFFIXES = ("_meta.xml", "_files.xml", "_thumb.png")


def human_size(n):
    n = float(n)
    for unit in ("B", "KB", "MB", "GB", "TB"):
        if n < 1024:
            return f"{n:.1f} {unit}"
        n /= 1024
    return f"{n:.1f} PB"


def file_ext(name):
    if "." in name:
        return name.rsplit(".", 1)[-1].lower()
    return "(none)"


@dataclass
class FileEntry:
    name: str
    size: int
    ext: str


@dataclass
class ItemResult:
    identifier: str
    title: str
    mediatype: str
    downloads: int
    file_count: int = 0
    total_bytes: int = 0
    top_files: list = field(default_factory=list)  # list of (name, size)
    all_files: list = field(default_factory=list)  # list of FileEntry
    files_loaded: bool = False
    error: str = ""

    @property
    def details_url(self):
        return DETAILS_URL.format(identifier=self.identifier)

    @property
    def download_dir_url(self):
        return DOWNLOAD_DIR_URL.format(identifier=self.identifier)

    @property
    def size_human(self):
        return human_size(self.total_bytes)

    def file_url(self, name):
        return f"{self.download_dir_url}/{quote(name)}"


def search_archive(query, mediatypes, rows, session):
    """Hit advancedsearch.php and return a list of ItemResult (metadata not yet fetched)."""
    clauses = [query] if query else []
    if mediatypes:
        mt_clause = " OR ".join(f"mediatype:({mt})" for mt in mediatypes)
        clauses.append(f"({mt_clause})")
    q = " AND ".join(clauses) if clauses else "mediatype:(texts)"

    params = {
        "q": q,
        "fl[]": ["identifier", "title", "mediatype", "downloads"],
        "rows": str(rows),
        "page": "1",
        "output": "json",
        "sort[]": "downloads desc",
    }
    resp = session.get(ADVANCED_SEARCH_URL, params=params, timeout=20)
    resp.raise_for_status()
    data = resp.json()
    docs = data.get("response", {}).get("docs", [])
    results = []
    for d in docs:
        results.append(
            ItemResult(
                identifier=d.get("identifier", ""),
                title=d.get("title", "(untitled)") or "(untitled)",
                mediatype=d.get("mediatype", "?"),
                downloads=int(d.get("downloads", 0) or 0),
            )
        )
    return results


def enrich_with_file_info(item: ItemResult, session):
    """Fetch the metadata record for an item: full file manifest, count, total size."""
    try:
        resp = session.get(METADATA_URL.format(identifier=item.identifier), timeout=20)
        resp.raise_for_status()
        meta = resp.json()
        files = meta.get("files", [])
        # Skip the usual derivative/noise files so counts reflect real content.
        real_files = [
            f for f in files
            if f.get("source") != "metadata" and not f.get("name", "").endswith(NOISE_SUFFIXES)
        ]
        entries = [
            FileEntry(name=f.get("name", ""), size=int(f.get("size", 0) or 0), ext=file_ext(f.get("name", "")))
            for f in real_files
        ]
        entries.sort(key=lambda e: e.size, reverse=True)
        item.all_files = entries
        item.file_count = len(entries)
        item.total_bytes = sum(e.size for e in entries)
        item.top_files = [(e.name, e.size) for e in entries[:5]]
        item.files_loaded = True
    except Exception as exc:  # noqa: BLE001 - surface any failure per-item, keep GUI alive
        item.error = str(exc)
        item.files_loaded = True


class TreasureFinderApp:
    COLUMN_LABELS = {
        "#0": "Title",
        "mediatype": "Type",
        "files": "Files",
        "size": "Size",
        "downloads": "Downloads",
    }
    NUMERIC_COLUMNS = {"files", "size", "downloads"}

    FILE_COLUMN_LABELS = {
        "#0": "File name",
        "ext": "Type",
        "size": "Size",
    }
    FILE_NUMERIC_COLUMNS = {"size"}

    def __init__(self, root):
        self.root = root
        root.title("Internet Archive Treasure Finder")
        root.geometry("1500x700")

        self.session = requests.Session()
        self.session.headers.update({"User-Agent": USER_AGENT})

        self.result_queue = queue.Queue()
        self.items_by_iid = {}
        self.iid_by_identifier = {}
        self.search_thread = None

        self.sort_col = "size"
        self.sort_reverse = True

        self.file_sort_col = "size"
        self.file_sort_reverse = True

        self.load_request_id = 0
        self.current_file_item = None
        self.ext_vars = {}

        self._build_layout()
        self.root.after(100, self._poll_queue)

    # ---------------------------------------------------------------- UI

    def _build_layout(self):
        paned = ttk.PanedWindow(self.root, orient=tk.HORIZONTAL)
        paned.pack(fill=tk.BOTH, expand=True)

        left = ttk.Frame(paned, padding=10)
        middle = ttk.Frame(paned, padding=10)
        right = ttk.Frame(paned, padding=10)
        paned.add(left, weight=1)
        paned.add(middle, weight=3)
        paned.add(right, weight=2)

        self._build_left_pane(left)
        self._build_results_pane(middle)
        self._build_file_browser_pane(right)

    def _build_left_pane(self, parent):
        ttk.Label(parent, text="Search term", font=("Segoe UI", 10, "bold")).pack(anchor="w")
        self.query_var = tk.StringVar()
        entry = ttk.Entry(parent, textvariable=self.query_var)
        entry.pack(fill=tk.X, pady=(0, 10))
        entry.bind("<Return>", lambda e: self.start_search())

        ttk.Label(parent, text="Media type", font=("Segoe UI", 10, "bold")).pack(anchor="w")
        self.mediatype_vars = {}
        for label, code in MEDIA_TYPES:
            var = tk.BooleanVar(value=(code in ("image", "texts", "movies")))
            self.mediatype_vars[code] = var
            ttk.Checkbutton(parent, text=label, variable=var).pack(anchor="w")

        ttk.Label(parent, text="Max candidates to scan", font=("Segoe UI", 10, "bold")).pack(
            anchor="w", pady=(10, 0)
        )
        self.rows_var = tk.IntVar(value=40)
        ttk.Spinbox(parent, from_=5, to=200, increment=5, textvariable=self.rows_var, width=10).pack(
            anchor="w"
        )

        self.fetch_files_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(
            parent,
            text="Inspect every candidate's file list up front\n(slower, but lets you sort all results by size)",
            variable=self.fetch_files_var,
        ).pack(anchor="w", pady=(10, 0))

        self.search_btn = ttk.Button(parent, text="Search", command=self.start_search)
        self.search_btn.pack(fill=tk.X, pady=(15, 5))

        self.status_var = tk.StringVar(value="Ready.")
        ttk.Label(parent, textvariable=self.status_var, wraplength=220, foreground="#555").pack(
            anchor="w", pady=(5, 0)
        )

        self.progress = ttk.Progressbar(parent, mode="determinate")
        self.progress.pack(fill=tk.X, pady=(10, 0))

        ttk.Separator(parent).pack(fill=tk.X, pady=15)
        ttk.Label(
            parent,
            text=(
                "Tip: click any column header in the results list to sort "
                "by it (e.g. Downloads). Click again to flip the order. "
                "Selecting a result loads its file list on the right, "
                "where you can filter by file type."
            ),
            wraplength=220,
            foreground="#777",
        ).pack(anchor="w")

    def _build_results_pane(self, parent):
        columns = ("mediatype", "files", "size", "downloads")
        self.tree = ttk.Treeview(parent, columns=columns, show="tree headings", height=18)
        for col, label in self.COLUMN_LABELS.items():
            self.tree.heading(col, text=label, command=lambda c=col: self._on_heading_click(c))
        self.tree.column("#0", width=340)
        self.tree.column("mediatype", width=70, anchor="center")
        self.tree.column("files", width=60, anchor="center")
        self.tree.column("size", width=90, anchor="center")
        self.tree.column("downloads", width=90, anchor="center")

        vsb = ttk.Scrollbar(parent, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=vsb.set)
        self.tree.grid(row=0, column=0, sticky="nsew")
        vsb.grid(row=0, column=1, sticky="ns")
        parent.rowconfigure(0, weight=3)
        parent.columnconfigure(0, weight=1)

        self.tree.bind("<<TreeviewSelect>>", self._on_select)
        self.tree.bind("<Double-1>", lambda e: self.open_details())

        detail_frame = ttk.Frame(parent)
        detail_frame.grid(row=1, column=0, columnspan=2, sticky="nsew", pady=(10, 0))
        parent.rowconfigure(1, weight=2)

        self.detail_text = tk.Text(detail_frame, height=10, wrap="word", font=("Consolas", 9))
        self.detail_text.pack(fill=tk.BOTH, expand=True, side=tk.LEFT)
        detail_vsb = ttk.Scrollbar(detail_frame, orient="vertical", command=self.detail_text.yview)
        self.detail_text.configure(yscrollcommand=detail_vsb.set)
        detail_vsb.pack(side=tk.RIGHT, fill=tk.Y)
        self.detail_text.configure(state="disabled")

        btn_frame = ttk.Frame(parent)
        btn_frame.grid(row=2, column=0, columnspan=2, sticky="w", pady=(8, 0))
        ttk.Button(btn_frame, text="Open details page", command=self.open_details).pack(
            side=tk.LEFT, padx=(0, 6)
        )
        ttk.Button(btn_frame, text="Open download directory", command=self.open_download_dir).pack(
            side=tk.LEFT
        )

        self._update_heading_labels()

    def _build_file_browser_pane(self, parent):
        ttk.Label(parent, text="Files in selected item", font=("Segoe UI", 10, "bold")).pack(anchor="w")

        filter_header = ttk.Frame(parent)
        filter_header.pack(fill=tk.X, pady=(4, 2))
        ttk.Label(filter_header, text="Filter by file type:").pack(side=tk.LEFT)
        ttk.Button(filter_header, text="All", width=5, command=lambda: self._set_all_ext_filters(True)).pack(
            side=tk.RIGHT, padx=(4, 0)
        )
        ttk.Button(filter_header, text="None", width=5, command=lambda: self._set_all_ext_filters(False)).pack(
            side=tk.RIGHT
        )

        # Scrollable checkbox area for detected extensions (varies per item).
        filter_canvas_frame = ttk.Frame(parent)
        filter_canvas_frame.pack(fill=tk.X, pady=(0, 8))
        self.filter_canvas = tk.Canvas(filter_canvas_frame, height=110, highlightthickness=0)
        filter_scroll = ttk.Scrollbar(filter_canvas_frame, orient="vertical", command=self.filter_canvas.yview)
        self.filter_inner = ttk.Frame(self.filter_canvas)
        self.filter_inner.bind(
            "<Configure>",
            lambda e: self.filter_canvas.configure(scrollregion=self.filter_canvas.bbox("all")),
        )
        self.filter_canvas.create_window((0, 0), window=self.filter_inner, anchor="nw")
        self.filter_canvas.configure(yscrollcommand=filter_scroll.set)
        self.filter_canvas.pack(side=tk.LEFT, fill=tk.X, expand=True)
        filter_scroll.pack(side=tk.RIGHT, fill=tk.Y)

        self.file_status_var = tk.StringVar(value="Select an item to see its files.")
        ttk.Label(parent, textvariable=self.file_status_var, foreground="#555").pack(anchor="w")

        file_tree_frame = ttk.Frame(parent)
        file_tree_frame.pack(fill=tk.BOTH, expand=True, pady=(4, 0))
        self.file_tree = ttk.Treeview(
            file_tree_frame, columns=("ext", "size"), show="tree headings", height=16
        )
        for col, label in self.FILE_COLUMN_LABELS.items():
            self.file_tree.heading(col, text=label, command=lambda c=col: self._on_file_heading_click(c))
        self.file_tree.column("#0", width=260)
        self.file_tree.column("ext", width=60, anchor="center")
        self.file_tree.column("size", width=80, anchor="center")
        file_vsb = ttk.Scrollbar(file_tree_frame, orient="vertical", command=self.file_tree.yview)
        self.file_tree.configure(yscrollcommand=file_vsb.set)
        self.file_tree.grid(row=0, column=0, sticky="nsew")
        file_vsb.grid(row=0, column=1, sticky="ns")
        file_tree_frame.rowconfigure(0, weight=1)
        file_tree_frame.columnconfigure(0, weight=1)
        self.file_tree.bind("<Double-1>", lambda e: self.open_selected_file())

        file_btn_frame = ttk.Frame(parent)
        file_btn_frame.pack(fill=tk.X, pady=(8, 0))
        ttk.Button(file_btn_frame, text="Download selected file", command=self.open_selected_file).pack(
            side=tk.LEFT, padx=(0, 6)
        )
        ttk.Button(file_btn_frame, text="Copy direct link", command=self.copy_selected_file_link).pack(
            side=tk.LEFT
        )

        self._update_file_heading_labels()

    # ------------------------------------------------------------ sorting

    def _on_heading_click(self, col):
        if self.sort_col == col:
            self.sort_reverse = not self.sort_reverse
        else:
            self.sort_col = col
            self.sort_reverse = col in self.NUMERIC_COLUMNS
        self._apply_sort()
        self._update_heading_labels()

    def _sort_key(self, iid, col):
        item = self.items_by_iid[iid]
        if col == "#0":
            return item.title.lower()
        if col == "mediatype":
            return item.mediatype.lower()
        if col == "files":
            return item.file_count
        if col == "size":
            return item.total_bytes
        if col == "downloads":
            return item.downloads
        return 0

    def _apply_sort(self):
        iids = list(self.items_by_iid.keys())
        iids.sort(key=lambda iid: self._sort_key(iid, self.sort_col), reverse=self.sort_reverse)
        for index, iid in enumerate(iids):
            self.tree.move(iid, "", index)

    def _update_heading_labels(self):
        for col, label in self.COLUMN_LABELS.items():
            if col == self.sort_col:
                arrow = " ▼" if self.sort_reverse else " ▲"
                self.tree.heading(col, text=label + arrow)
            else:
                self.tree.heading(col, text=label)

    def _on_file_heading_click(self, col):
        if self.file_sort_col == col:
            self.file_sort_reverse = not self.file_sort_reverse
        else:
            self.file_sort_col = col
            self.file_sort_reverse = col in self.FILE_NUMERIC_COLUMNS
        self._update_file_heading_labels()
        self._apply_file_filter()

    def _file_sort_key(self, f):
        if self.file_sort_col == "#0":
            return f.name.lower()
        if self.file_sort_col == "ext":
            return f.ext.lower()
        if self.file_sort_col == "size":
            return f.size
        return 0

    def _update_file_heading_labels(self):
        for col, label in self.FILE_COLUMN_LABELS.items():
            if col == self.file_sort_col:
                arrow = " ▼" if self.file_sort_reverse else " ▲"
                self.file_tree.heading(col, text=label + arrow)
            else:
                self.file_tree.heading(col, text=label)

    # ------------------------------------------------------------ actions

    def start_search(self):
        if self.search_thread and self.search_thread.is_alive():
            return
        query = self.query_var.get().strip()
        selected_types = [code for code, var in self.mediatype_vars.items() if var.get()]
        if not query and not selected_types:
            messagebox.showinfo("Nothing to search", "Enter a search term or pick a media type.")
            return

        for row in self.tree.get_children():
            self.tree.delete(row)
        self.items_by_iid.clear()
        self.iid_by_identifier.clear()
        self._set_detail_text("")
        self._clear_file_panel("Select an item to see its files.")
        self.progress.configure(value=0, maximum=100)
        self.search_btn.configure(state="disabled")
        self.status_var.set("Searching archive.org...")

        fetch_files = self.fetch_files_var.get()
        self.sort_col = "size" if fetch_files else "downloads"
        self.sort_reverse = True

        self.search_thread = threading.Thread(
            target=self._run_search,
            args=(query, selected_types, self.rows_var.get(), fetch_files),
            daemon=True,
        )
        self.search_thread.start()

    def _run_search(self, query, mediatypes, rows, fetch_files):
        try:
            results = search_archive(query, mediatypes, rows, self.session)
        except Exception as exc:  # noqa: BLE001
            self.result_queue.put(("error", str(exc)))
            return

        if not results:
            self.result_queue.put(("done", []))
            return

        if fetch_files:
            total = len(results)
            for i, item in enumerate(results, start=1):
                enrich_with_file_info(item, self.session)
                self.result_queue.put(("progress", i, total))
            results.sort(key=lambda r: r.total_bytes, reverse=True)
        else:
            results.sort(key=lambda r: r.downloads, reverse=True)

        self.result_queue.put(("done", results))

    def _poll_queue(self):
        try:
            while True:
                msg = self.result_queue.get_nowait()
                kind = msg[0]
                if kind == "progress":
                    i, total = msg[1], msg[2]
                    self.progress.configure(maximum=total, value=i)
                    self.status_var.set(f"Inspecting file lists... {i}/{total}")
                elif kind == "error":
                    self.search_btn.configure(state="normal")
                    self.status_var.set("Search failed.")
                    messagebox.showerror("Search failed", msg[1])
                elif kind == "done":
                    self._populate_results(msg[1])
                    self.search_btn.configure(state="normal")
                elif kind == "files_loaded":
                    self._handle_files_loaded(msg[1], msg[2])
        except queue.Empty:
            pass
        self.root.after(100, self._poll_queue)

    def _populate_results(self, results):
        if not results:
            self.status_var.set("No matches found.")
            return
        for item in results:
            iid = self.tree.insert(
                "",
                "end",
                text=item.title[:80],
                values=(
                    item.mediatype,
                    item.file_count or "-",
                    item.size_human if item.total_bytes else "-",
                    item.downloads,
                ),
            )
            self.items_by_iid[iid] = item
            self.iid_by_identifier[item.identifier] = iid
        self._update_heading_labels()
        self.status_var.set(f"Found {len(results)} items. Click column headers to re-sort.")

    def _on_select(self, event=None):
        item = self._current_item()
        if not item:
            return
        self._render_detail_text(item)

        if item.files_loaded:
            self._show_files_for_item(item)
        else:
            self._clear_file_panel("Loading file list...")
            self.load_request_id += 1
            req_id = self.load_request_id
            threading.Thread(target=self._bg_load_files, args=(item, req_id), daemon=True).start()

    def _bg_load_files(self, item, req_id):
        enrich_with_file_info(item, self.session)
        self.result_queue.put(("files_loaded", req_id, item))

    def _handle_files_loaded(self, req_id, item):
        if req_id != self.load_request_id:
            return  # a newer selection superseded this request
        iid = self.iid_by_identifier.get(item.identifier)
        if iid is not None:
            self.tree.item(
                iid,
                values=(
                    item.mediatype,
                    item.file_count or "-",
                    item.size_human if item.total_bytes else "-",
                    item.downloads,
                ),
            )
        current = self._current_item()
        if current is item:
            self._render_detail_text(item)
            self._show_files_for_item(item)

    def _render_detail_text(self, item):
        lines = [
            f"Title: {item.title}",
            f"Identifier: {item.identifier}",
            f"Media type: {item.mediatype}",
            f"Downloads (all-time): {item.downloads}",
            "",
            f"Details page:    {item.details_url}",
            f"Download folder: {item.download_dir_url}",
            "",
        ]
        if item.error:
            lines.append(f"(Could not inspect files: {item.error})")
        elif item.files_loaded:
            lines.append(f"Files: {item.file_count}   Total size: {item.size_human}")
            lines.append("Largest files in this item:")
            for name, size in item.top_files:
                lines.append(f"  - {name}  ({human_size(size)})")
                lines.append(f"      {item.file_url(name)}")
        else:
            lines.append("(Loading file list...)")

        self._set_detail_text("\n".join(lines))

    def _set_detail_text(self, text):
        self.detail_text.configure(state="normal")
        self.detail_text.delete("1.0", tk.END)
        self.detail_text.insert("1.0", text)
        self.detail_text.configure(state="disabled")

    def _current_item(self):
        sel = self.tree.selection()
        if not sel:
            return None
        return self.items_by_iid.get(sel[0])

    def open_details(self):
        item = self._current_item()
        if item:
            webbrowser.open(item.details_url)

    def open_download_dir(self):
        item = self._current_item()
        if item:
            webbrowser.open(item.download_dir_url)

    # ------------------------------------------------------- file browser

    def _clear_file_panel(self, status_text):
        for row in self.file_tree.get_children():
            self.file_tree.delete(row)
        for widget in self.filter_inner.winfo_children():
            widget.destroy()
        self.ext_vars = {}
        self.current_file_item = None
        self.file_status_var.set(status_text)

    def _show_files_for_item(self, item):
        self.current_file_item = item

        if item.error:
            self._clear_file_panel(f"Could not load files: {item.error}")
            self.current_file_item = item
            return

        extensions = sorted({f.ext for f in item.all_files})
        for widget in self.filter_inner.winfo_children():
            widget.destroy()
        self.ext_vars = {}

        cols = 3
        for i, ext in enumerate(extensions):
            var = tk.BooleanVar(value=True)
            self.ext_vars[ext] = var
            label = f".{ext}" if ext != "(none)" else ext
            cb = ttk.Checkbutton(self.filter_inner, text=label, variable=var, command=self._apply_file_filter)
            cb.grid(row=i // cols, column=i % cols, sticky="w", padx=4, pady=1)

        self._apply_file_filter()

    def _set_all_ext_filters(self, value):
        for var in self.ext_vars.values():
            var.set(value)
        self._apply_file_filter()

    def _apply_file_filter(self):
        for row in self.file_tree.get_children():
            self.file_tree.delete(row)
        item = self.current_file_item
        if not item:
            return
        active = {ext for ext, var in self.ext_vars.items() if var.get()}
        shown = [f for f in item.all_files if f.ext in active]
        shown.sort(key=self._file_sort_key, reverse=self.file_sort_reverse)
        for f in shown:
            self.file_tree.insert("", "end", text=f.name, values=(f.ext, human_size(f.size)))
        self.file_status_var.set(f"Showing {len(shown)} of {len(item.all_files)} files")

    def _current_file(self):
        sel = self.file_tree.selection()
        if not sel or not self.current_file_item:
            return None
        name = self.file_tree.item(sel[0], "text")
        return name

    def open_selected_file(self):
        name = self._current_file()
        if name and self.current_file_item:
            webbrowser.open(self.current_file_item.file_url(name))

    def copy_selected_file_link(self):
        name = self._current_file()
        if name and self.current_file_item:
            url = self.current_file_item.file_url(name)
            self.root.clipboard_clear()
            self.root.clipboard_append(url)
            self.status_var.set(f"Copied link: {url}")


def main():
    root = tk.Tk()
    try:
        ttk.Style().theme_use("vista")
    except tk.TclError:
        pass
    TreasureFinderApp(root)
    root.mainloop()


if __name__ == "__main__":
    main()
