import os
import re
import json
import locale
import subprocess
import traceback
import tkinter as tk
import tkinter.font as tkfont
import numpy as np
import pandas as pd
import matplotlib.pyplot as plt
import matplotlib.dates as mdates
from tkinter import Tk, StringVar
from tkinter import filedialog, messagebox
from tkinter import ttk
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
from matplotlib.figure import Figure
from matplotlib.collections import LineCollection
from pandas.api.types import is_numeric_dtype

try:
    from tkcalendar import Calendar
except Exception:
    Calendar = None


def _normalize_col_name(name):
    text = str(name).strip().lower()
    return " ".join(text.replace("_", " ").replace("-", " ").split())


def _coerce_numeric_ratio(series):
    if series is None:
        return 0.0
    clean = series.dropna()
    if clean.empty:
        return 0.0
    prepared = (
        clean.astype(str)
        .str.replace("\u00a0", "", regex=False)
        .str.replace(" ", "", regex=False)
        .str.replace(",", ".", regex=False)
    )
    converted = pd.to_numeric(prepared, errors="coerce")
    return float(converted.notna().mean())


def _date_parse_ratio(series, sample_limit=300):
    if series is None:
        return 0.0
    clean = series.dropna()
    if clean.empty:
        return 0.0

    if len(clean) > sample_limit:
        clean = clean.sample(sample_limit, random_state=0)

    text = clean.astype(str).str.strip()
    text = text[text != ""]
    if text.empty:
        return 0.0

    # Skip obvious non-date columns early to avoid expensive element-wise parser.
    date_like_mask = text.str.contains(r"\d{1,4}[./\-]\d{1,2}[./\-]\d{1,4}", regex=True)
    time_like_mask = text.str.contains(r"\d{1,2}:\d{2}", regex=True)
    if float((date_like_mask | time_like_mask).mean()) < 0.4:
        return 0.0

    parsed = pd.to_datetime(text, errors="coerce", format="mixed", dayfirst=True)
    return float(parsed.notna().mean())


def _find_header_row(lines):
    markers = ("бюджет", "дата", "кфср", "кцср", "квр", "косгу")
    best_idx = 0
    best_score = -1
    for idx, raw in enumerate(lines[:80]):
        line = raw.strip().lower()
        if not line:
            continue
        score = sum(1 for m in markers if m in line)
        if score > best_score:
            best_score = score
            best_idx = idx
    return best_idx if best_score >= 2 else 0


def _convert_numeric_like_columns(df):
    if df is None or df.empty:
        return df
    out = df.copy()
    for col in out.columns:
        s = out[col]
        if is_numeric_dtype(s):
            continue
        prepared = (
            s.astype(str)
            .str.strip()
            .str.replace("\u00a0", "", regex=False)
            .str.replace(" ", "", regex=False)
            .str.replace(",", ".", regex=False)
        )
        converted = pd.to_numeric(prepared, errors="coerce")
        if converted.notna().mean() >= 0.85:
            out[col] = converted
    return out


def _normalize_loaded_df(df):
    if df is None or df.empty:
        return df
    work = df.copy()
    work = work.dropna(how="all")
    if len(work.columns) > 0:
        first_col = work.columns[0]
        mask_bad = work[first_col].astype(str).str.lower().str.contains(
            "итого|дата печати|наименование органа|на \\d{2}\\.\\d{2}\\.\\d{4}",
            regex=True,
            na=False,
        )
        work = work[~mask_bad]
    work = work.reset_index(drop=True)
    work = _convert_numeric_like_columns(work)
    return work


def _transform_rchb_to_buau_like(df):
    if df is None or df.empty:
        return df
    required = {"Бюджет", "Дата проводки", "КФСР", "КЦСР", "КВР", "КОСГУ", "КВФО"}
    if not required.issubset(set(df.columns)):
        return df
    if "Всего выбытий (бух.уч.)" not in df.columns:
        return df

    org_col = "Наименование КВСР" if "Наименование КВСР" in df.columns else None
    subsidy_col = "Код цели" if "Код цели" in df.columns else None

    out = pd.DataFrame()
    out["Бюджет"] = df["Бюджет"]
    out["Дата проводки"] = df["Дата проводки"]
    out["КФСР"] = df["КФСР"]
    out["КЦСР"] = df["КЦСР"]
    out["КВР"] = df["КВР"]
    out["КОСГУ"] = df["КОСГУ"]
    out["Код субсидии"] = df[subsidy_col] if subsidy_col else ""
    out["Отраслевой код"] = "00000000000000000"
    out["КВФО"] = df["КВФО"]
    out["Организация"] = df[org_col] if org_col else ""
    out["Орган, предоставляющий субсидии"] = df["Бюджет"]
    out["Выплаты с учетом возврата"] = df["Всего выбытий (бух.уч.)"]
    out["Выплаты - Исполнение"] = df["Всего выбытий (бух.уч.)"]
    out["Выплаты - Восстановление выплат - год"] = 0.0
    return _convert_numeric_like_columns(out)


class DataAnalyzerApp:
    def __init__(self, root):
        self.root = root
        self.app_name = "Prisma"
        self.root.title(self.app_name)
        self.root.geometry("1200x800")
        # Better full-screen use on Windows.
        try:
            self.root.state("zoomed")
        except Exception:
            pass

        self.data = None
        self.filtered_data = None

        self.object_column = None
        self.date_column = None
        self.param_columns = []

        self.status_var = StringVar(value="Данные не загружены")
        self.ui_scale = 1.0
        self.base_font_sizes = {}
        self.settings_path = os.path.join(os.path.expanduser("~"), ".prisma_settings.json")
        self.settings = self._load_settings()
        self.current_language_code = "ru"
        self.translation_lang_options = self._build_translation_language_options()
        self.ui_text_map = self._build_ui_text_map()
        self._restore_language_from_settings()
        self._set_window_icon()

        # Theme handling
        self.theme_mode = "light"  # "light" | "dark"
        self.style = ttk.Style(self.root)
        try:
            # Clam respects custom ttk colors on Windows better than native themes.
            self.style.theme_use("clam")
        except Exception:
            pass
        self._apply_theme()

        self.create_widgets()
        self.create_plot_area()
        self.create_table_area()
        self._bind_zoom_shortcuts()
        self.root.after(400, self._ask_startup_language)

        # Ensure plot colors match the theme after widgets exist.
        self._apply_matplotlib_theme_colors()

    def _set_window_icon(self):
        try:
            icon_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "prisma_icon.png")
            if os.path.exists(icon_path):
                self._icon_image = tk.PhotoImage(file=icon_path)
                self.root.iconphoto(True, self._icon_image)
        except Exception:
            pass

    def _load_settings(self):
        default = {"language_code": "", "remember_language": False, "show_startup_help": True}
        try:
            if os.path.exists(self.settings_path):
                with open(self.settings_path, "r", encoding="utf-8") as f:
                    loaded = json.load(f)
                    if isinstance(loaded, dict):
                        default.update(loaded)
        except Exception:
            pass
        return default

    def _save_settings(self):
        try:
            with open(self.settings_path, "w", encoding="utf-8") as f:
                json.dump(self.settings, f, ensure_ascii=False, indent=2)
        except Exception:
            pass

    def _restore_language_from_settings(self):
        code = str(self.settings.get("language_code", "")).strip().lower()
        if code:
            self.current_language_code = code

    def _build_translation_language_options(self):
        device_codes = []
        # Windows: try to fetch full user language list.
        try:
            ps_cmd = (
                "Get-WinUserLanguageList | "
                "ForEach-Object { $_.LanguageTag }"
            )
            out = subprocess.check_output(
                ["powershell", "-NoProfile", "-Command", ps_cmd],
                stderr=subprocess.DEVNULL,
                text=True,
                encoding="utf-8",
                timeout=2.5,
            )
            for line in out.splitlines():
                lang_tag = line.strip()
                if lang_tag:
                    device_codes.append(lang_tag)
        except Exception:
            pass

        # Fallbacks: current process locale values.
        try:
            windows_lang, _enc = locale.getlocale()
            if windows_lang:
                device_codes.append(windows_lang.replace("_", "-"))
        except Exception:
            pass
        try:
            env_lang = locale.setlocale(locale.LC_CTYPE, None)
            if env_lang:
                device_codes.append(str(env_lang).split(".")[0].replace("_", "-"))
        except Exception:
            pass
        options = []
        seen_codes = set()
        for code in device_codes:
            code = str(code).strip()
            if not code:
                continue
            short = self._normalize_lang_short(code)
            if short in seen_codes:
                continue
            seen_codes.add(short)
            options.append(f"{code} ({short})")
        return options or ["en-US (en)"]

    def _normalize_lang_short(self, code_text):
        raw = str(code_text).strip()
        # Examples: "ru-RU", "ru_RU", "ru", "Русский (Россия)"
        m = re.match(r"([a-zA-Z]{2,3})(?:[-_].*)?$", raw)
        if m:
            return m.group(1).lower()
        m2 = re.search(r"\b([a-zA-Z]{2,3})\b", raw)
        if m2:
            return m2.group(1).lower()
        return "en"

    def _extract_lang_code(self, text):
        match = re.search(r"\(([^)]+)\)\s*$", str(text))
        if match:
            return match.group(1).strip().lower()
        return "ru"

    def _build_ui_text_map(self):
        return {
            "Конструктор аналитических выборок": "Analytics Selection Builder",
            "Управление": "Controls",
            "Данные не выбраны": "No data selected",
            "Загрузить данные": "Load data",
            "Объект:": "Object:",
            "Дата(ы):": "Date(s):",
            "Показатели:": "Metrics:",
            "Получить выборку": "Build selection",
            "Экспорт в Excel": "Export to Excel",
            "Очистить фильтры": "Clear filters",
            "Столбцы не определены": "Columns are not detected",
            "График": "Chart",
            "Предпросмотр выборки": "Selection preview",
            "Легенда графика": "Chart legend",
            "Изменения по датам": "Changes by dates",
            "Справка": "Help",
            "Закрыть": "Close",
            "Справка: Объекты и параметры": "Help: Objects and metrics",
            "Как пользоваться фильтрами и графиком": "How to use filters and chart",
            "Язык перевода:": "Translation language:",
            "Данные не загружены": "Data is not loaded",
            "Объект: часть названия/кода (можно вводить не полностью).": "Object: partial name/code is allowed.",
            "Дата(ы): одна дата, список через запятую или диапазон через '-' . Пример: 01.01.2026 - 31.01.2026":
                "Date(s): single date, comma-separated list, or range with '-'. Example: 01.01.2026 - 31.01.2026",
            "Параметры: названия числовых столбцов через запятую.": "Metrics: enter numeric column names separated by commas.",
            "Языки: доступны только языки, найденные на устройстве.": "Languages: only device languages are available.",
            "Линии не построены.": "No lines plotted.",
            "Подсказка по графику:\n1. Загрузите данные.\n2. Выберите объект, показатели и дату(ы).\n3. Выберите язык перевода (из языков устройства).\n4. Нажмите 'Получить выборку' (график строится автоматически).":
                "Chart tips:\n1. Load data.\n2. Select object, metrics, and date(s).\n3. Choose interface language (from device languages).\n4. Click 'Build selection' (chart is built automatically).",
        }

    def _is_ru(self):
        return str(getattr(self, "current_language_code", "ru")).startswith("ru")

    def _tr(self, ru_text, en_text):
        return ru_text if self._is_ru() else en_text

    def _show_info(self, ru_title, en_title, ru_message, en_message):
        messagebox.showinfo(self._tr(ru_title, en_title), self._tr(ru_message, en_message))

    def _show_warning(self, ru_title, en_title, ru_message, en_message):
        messagebox.showwarning(self._tr(ru_title, en_title), self._tr(ru_message, en_message))

    def _show_error(self, ru_title, en_title, ru_message, en_message):
        messagebox.showerror(self._tr(ru_title, en_title), self._tr(ru_message, en_message))

    def _translate_data_text(self, value):
        if self._is_ru():
            return value
        text = str(value)
        data_map = {
            "Бюджет": "Budget",
            "Дата проводки": "Posting date",
            "КФСР": "KFSR",
            "КЦСР": "KCSR",
            "КВР": "KVR",
            "КОСГУ": "KOSGU",
            "КВФО": "KVFO",
            "Код субсидии": "Subsidy code",
            "Организация": "Organization",
            "Орган, предоставляющий субсидии": "Subsidy provider",
            "Выплаты с учетом возврата": "Payments incl. returns",
            "Выплаты - Исполнение": "Payments - execution",
            "Выплаты - Восстановление выплат - год": "Payments - recovery - year",
        }
        return data_map.get(text, text)

    def _apply_language_to_widgets(self):
        is_ru = self._is_ru()
        mapping = {v: k for k, v in self.ui_text_map.items()} if is_ru else self.ui_text_map

        def walk(widget):
            try:
                text = widget.cget("text")
                if text in mapping:
                    widget.configure(text=mapping[text])
            except Exception:
                pass
            for child in widget.winfo_children():
                walk(child)

        walk(self.root)
        self.root.title(self.app_name)
        current_status = self.status_var.get()
        if current_status in mapping:
            self.status_var.set(mapping[current_status])

    def _on_language_change(self, _event=None):
        if hasattr(self, "target_lang_combo"):
            selected = self.target_lang_combo.get().strip()
            self.current_language_code = self._extract_lang_code(selected)
            self._apply_language_to_widgets()
            if self.settings.get("remember_language"):
                self.settings["language_code"] = self.current_language_code
                self._save_settings()

    def _build_startup_help_text(self):
        is_ru = self.current_language_code.startswith("ru")
        chosen_lang = self.target_lang_combo.get().strip() if hasattr(self, "target_lang_combo") else "Русский (ru)"
        if is_ru:
            return (
                "Быстрый старт:\n"
                "1) Загрузите CSV (один файл или папку).\n"
                "2) Выберите объект, дату(ы) и показатели.\n"
                f"3) Язык интерфейса и подсказок: {chosen_lang}\n"
                "4) Нажмите 'Получить выборку'. График строится автоматически.\n"
                "5) При необходимости экспортируйте результат в Excel."
            )
        return (
            "Quick start:\n"
            "1) Load CSV (single file or folder).\n"
            "2) Select object, date(s), and metrics.\n"
            f"3) Interface/help language: {chosen_lang}\n"
            "4) Click 'Build selection'. The chart is built automatically.\n"
            "5) Export to Excel if needed."
        )

    def _show_startup_help(self):
        if getattr(self, "_startup_help_shown", False):
            return
        if not self.settings.get("show_startup_help", True):
            return
        self._startup_help_shown = True
        is_ru = self.current_language_code.startswith("ru")
        messagebox.showinfo(
            "Справка при запуске" if is_ru else "Startup help",
            self._build_startup_help_text(),
        )

    def _ask_startup_language(self):
        if not hasattr(self, "target_lang_combo"):
            self._show_startup_help()
            return
        if self.settings.get("remember_language") and self.settings.get("language_code"):
            remembered_code = str(self.settings.get("language_code", "")).strip().lower()
            for option in self.translation_lang_options:
                if self._extract_lang_code(option) == remembered_code:
                    self.target_lang_combo.set(option)
                    self._on_language_change()
                    break
            self._show_startup_help()
            return
        win = tk.Toplevel(self.root)
        win.title("Выбор языка / Choose language")
        win.transient(self.root)
        win.grab_set()
        ttk.Label(win, text="Выберите язык интерфейса:").grid(row=0, column=0, sticky="w", padx=10, pady=(10, 4))
        chooser = ttk.Combobox(win, state="readonly", style="App.TCombobox", values=self.translation_lang_options)
        chooser.grid(row=1, column=0, sticky="ew", padx=10, pady=(0, 10))
        current_option = self.translation_lang_options[0] if self.translation_lang_options else "en-US (en)"
        for option in self.translation_lang_options:
            if self._extract_lang_code(option) == self.current_language_code:
                current_option = option
                break
        chooser.set(current_option)

        remember_lang_var = tk.BooleanVar(value=bool(self.settings.get("remember_language", False)))
        show_help_var = tk.BooleanVar(value=bool(self.settings.get("show_startup_help", True)))
        ttk.Checkbutton(
            win,
            text="Запомнить выбор языка / Remember selected language",
            variable=remember_lang_var,
        ).grid(row=2, column=0, sticky="w", padx=10, pady=(0, 4))
        ttk.Checkbutton(
            win,
            text="Показывать короткую справку при запуске / Show quick help at startup",
            variable=show_help_var,
        ).grid(row=3, column=0, sticky="w", padx=10, pady=(0, 10))
        win.columnconfigure(0, weight=1)

        def _apply_and_close():
            self.target_lang_combo.set(chooser.get())
            self._on_language_change()
            self.settings["remember_language"] = bool(remember_lang_var.get())
            self.settings["show_startup_help"] = bool(show_help_var.get())
            self.settings["language_code"] = self.current_language_code
            self._save_settings()
            win.destroy()
            self._show_startup_help()

        ttk.Button(win, text="OK", command=_apply_and_close, style="App.TButton").grid(
            row=4, column=0, sticky="e", padx=10, pady=(0, 10)
        )

    def choose_load_method(self):
        is_ru = self._is_ru()
        win = tk.Toplevel(self.root)
        win.title("Выбор способа загрузки" if is_ru else "Load method")
        win.transient(self.root)
        win.grab_set()
        win.resizable(False, False)

        text = (
            "Выберите способ загрузки данных:"
            if is_ru
            else "Choose how to load data:"
        )
        ttk.Label(win, text=text).grid(row=0, column=0, columnspan=3, sticky="w", padx=12, pady=(12, 8))

        selected = {"mode": None}

        def _choose(mode):
            selected["mode"] = mode
            win.destroy()

        ttk.Button(
            win,
            text="Один файл" if is_ru else "Single file",
            command=lambda: _choose("single"),
            style="App.TButton",
        ).grid(row=1, column=0, padx=(12, 6), pady=(0, 12))
        ttk.Button(
            win,
            text="Папка (все CSV)" if is_ru else "Folder (all CSV)",
            command=lambda: _choose("folder"),
            style="App.TButton",
        ).grid(row=1, column=1, padx=6, pady=(0, 12))
        ttk.Button(
            win,
            text="Отмена" if is_ru else "Cancel",
            command=lambda: _choose("cancel"),
            style="App.TButton",
        ).grid(row=1, column=2, padx=(6, 12), pady=(0, 12))

        self.root.wait_window(win)
        if selected["mode"] == "single":
            self.load_single_file()
        elif selected["mode"] == "folder":
            self.load_file_from_folder()

    def read_csv_safe(self, file_path):
        encodings = ["utf-8", "utf-8-sig", "cp1251", "windows-1251"]
        last_error = None

        for encoding in encodings:
            try:
                with open(file_path, "r", encoding=encoding, errors="replace") as f:
                    preview_lines = [f.readline() for _ in range(80)]

                header_row = _find_header_row(preview_lines)
                sample_text = "\n".join(preview_lines[:20])
                delim_scores = {
                    ";": sample_text.count(";"),
                    "\t": sample_text.count("\t"),
                    ",": sample_text.count(","),
                }
                delimiter = max(delim_scores, key=delim_scores.get)

                df = pd.read_csv(
                    file_path,
                    encoding=encoding,
                    sep=delimiter,
                    engine="python",
                    skiprows=header_row,
                    dtype=str,
                )
                df.columns = [str(col).strip() for col in df.columns]
                df = _normalize_loaded_df(df)
                df = _transform_rchb_to_buau_like(df)
                return df
            except Exception as e:
                last_error = e

        raise last_error

    def detect_columns(self):
        self.object_column = None
        self.date_column = None
        self.param_columns = []

        if self.data is None or self.data.empty:
            return

        object_keywords = (
            "объект", "object", "name", "название", "код", "id", "станция", "unit", "device"
        )
        date_keywords = (
            "дата", "date", "datetime", "timestamp", "время", "time", "period", "день", "месяц"
        )

        n_rows = len(self.data)
        obj_best = (0.0, None)
        date_best = (0.0, None)
        date_ratio_by_col = {}

        for col in self.data.columns:
            if str(col) == "__source_file__":
                continue

            col_name = _normalize_col_name(col)
            series = self.data[col]
            non_null = series.dropna()
            nunq = non_null.astype(str).nunique() if not non_null.empty else 0
            date_ratio = _date_parse_ratio(series)
            date_ratio_by_col[col] = date_ratio

            obj_score = 0.0
            if any(k in col_name for k in object_keywords):
                obj_score += 5.0
            if not is_numeric_dtype(series):
                obj_score += 1.0
            if 1 < nunq <= max(2, int(n_rows * 0.9)):
                obj_score += 2.0
            if nunq == n_rows:
                obj_score -= 0.5
            if any(k in col_name for k in date_keywords):
                obj_score -= 3.0
            if date_ratio >= 0.6:
                obj_score -= 3.5
            if obj_score > obj_best[0]:
                obj_best = (obj_score, col)

            date_score = 0.0
            if any(k in col_name for k in date_keywords):
                date_score += 4.0
            date_score += date_ratio * 3.0
            if date_score > date_best[0]:
                date_best = (date_score, col)

        if obj_best[1] is not None and obj_best[0] >= 2.0:
            self.object_column = obj_best[1]
        if date_best[1] is not None and date_best[0] >= 2.5:
            self.date_column = date_best[1]

        detected_params = []
        for col in self.data.columns:
            if col in ("__source_file__", self.object_column, self.date_column):
                continue
            series = self.data[col]
            if date_ratio_by_col.get(col, 0.0) >= 0.6:
                continue
            if is_numeric_dtype(series):
                detected_params.append(str(col))
                continue
            ratio = _coerce_numeric_ratio(series)
            if ratio >= 0.85:
                detected_params.append(str(col))
        self.param_columns = detected_params

    def load_single_file(self):
        file_path = filedialog.askopenfilename(
            filetypes=[("CSV files", "*.csv"), ("All files", "*.*")]
        )
        if not file_path:
            return

        try:
            self.data = self.read_csv_safe(file_path)
            self.data["__source_file__"] = os.path.basename(file_path)
            self.filtered_data = None
            self.detect_columns()
            self.file_label.config(text=f"Загружен: {os.path.basename(file_path)}")
            self.update_status(
                f"Загружено строк: {len(self.data)}"
                if self._is_ru()
                else f"Loaded rows: {len(self.data)}"
            )
            self.update_columns_hint()
            self.clear_table()
            self.clear_plot()
            self._show_info("Успех", "Success", "Файл успешно загружен!", "File loaded successfully!")
        except Exception as e:
            self._show_error("Ошибка", "Error", f"Не удалось загрузить файл:\n{e}", f"Failed to load file:\n{e}")

    def load_file_from_folder(self):
        folder_path = filedialog.askdirectory()
        if not folder_path:
            return

        try:
            all_files = [f for f in os.listdir(folder_path) if f.lower().endswith(".csv")]
            if not all_files:
                self._show_warning("Нет файлов", "No files", "В папке не найдено CSV-файлов.", "No CSV files found in the folder.")
                return

            dataframes = []
            for file_name in all_files:
                file_path = os.path.join(folder_path, file_name)
                df = self.read_csv_safe(file_path)
                df["__source_file__"] = file_name
                dataframes.append(df)

            self.data = pd.concat(dataframes, ignore_index=True, sort=False)
            self.filtered_data = None
            self.detect_columns()
            self.file_label.config(text=f"Загружено из папки: {len(all_files)} файлов")
            self.update_status(
                f"Загружено строк: {len(self.data)}"
                if self._is_ru()
                else f"Loaded rows: {len(self.data)}"
            )
            self.update_columns_hint()
            self.clear_table()
            self.clear_plot()
            self._show_info(
                "Успех",
                "Success",
                f"Успешно загружено {len(all_files)} файлов!",
                f"Successfully loaded {len(all_files)} files!",
            )
        except Exception as e:
            self._show_error("Ошибка", "Error", f"Не удалось загрузить файлы:\n{e}", f"Failed to load files:\n{e}")

    def create_widgets(self):
        main = ttk.Frame(self.root, padding=10)
        main.pack(fill="both", expand=True)

        top_frame = ttk.LabelFrame(main, text="Управление", padding=10)
        top_frame.pack(fill="x", pady=(0, 10))

        self.file_label = ttk.Label(top_frame, text="Данные не выбраны")
        self.file_label.grid(row=0, column=0, columnspan=4, sticky="w", pady=(0, 8))

        top_right = ttk.Frame(top_frame)
        top_right.grid(row=0, column=4, sticky="e", padx=(10, 0))

        ttk.Button(top_right, text="Загрузить данные", command=self.choose_load_method).pack(
            side="left", padx=(0, 10)
        )

        self.theme_toggle_btn = ttk.Button(
            top_right,
            width=3,
            text="☀",
            command=self._toggle_theme,
        )
        self.theme_toggle_btn.pack(side="left")

        ttk.Label(top_frame, text="Объект:").grid(row=1, column=0, sticky="e", padx=5, pady=5)
        self.obj_entry = ttk.Entry(top_frame)
        self.obj_entry.grid(row=1, column=1, sticky="ew", padx=5, pady=5)

        ttk.Label(top_frame, text="Дата(ы):").grid(row=1, column=2, sticky="e", padx=5, pady=5)
        self.date_entry = ttk.Entry(top_frame)
        self.date_entry.grid(row=1, column=3, sticky="ew", padx=5, pady=5)
        ttk.Button(top_frame, text="📅", width=3, command=lambda: _open_calendar_for_entry(self, self.date_entry)).grid(
            row=1, column=4, sticky="w", padx=(4, 0), pady=5
        )

        ttk.Label(top_frame, text="Показатели:").grid(row=2, column=0, sticky="e", padx=5, pady=5)
        self.param_entry = ttk.Entry(top_frame)
        self.param_entry.grid(row=2, column=1, columnspan=4, sticky="ew", padx=5, pady=(7, 5), ipady=2)

        self.dates_list_entry = None
        self.date_from_entry = None
        self.date_to_entry = None

        button_frame = ttk.Frame(top_frame)
        button_frame.grid(row=3, column=0, columnspan=5, sticky="ew", pady=(12, 0))

        ttk.Button(button_frame, text="Получить выборку", command=self.get_selection_and_update).pack(
            side="left", padx=5
        )
        ttk.Button(button_frame, text="Экспорт в Excel", command=self.export_to_excel).pack(
            side="left", padx=5
        )
        ttk.Button(button_frame, text="Очистить фильтры", command=self.clear_filters).pack(
            side="left", padx=5
        )

        self.columns_hint = ttk.Label(top_frame, text="Столбцы не определены")
        self.columns_hint.grid(row=4, column=0, columnspan=5, sticky="w", pady=(8, 0))

        self.status_label = ttk.Label(main, textvariable=self.status_var)
        self.status_label.pack(fill="x", pady=(0, 10))

        for col in range(5):
            top_frame.columnconfigure(col, weight=1)

        content_frame = ttk.PanedWindow(main, orient="vertical")
        content_frame.pack(fill="both", expand=True)

        self.plot_container = ttk.LabelFrame(content_frame, text="График", padding=10)
        self.table_container = ttk.LabelFrame(content_frame, text="Предпросмотр выборки", padding=10)

        # Делаем верхнюю часть (график + изменения по датам) максимально приоритетной,
        # а предпросмотр выборки компактным.
        self.table_container.configure(height=130)
        content_frame.add(self.plot_container, weight=14)
        content_frame.add(self.table_container, weight=1)

    def create_plot_area(self):
        plot_layout = ttk.Frame(self.plot_container)
        plot_layout.pack(fill="both", expand=True)

        chart_frame = ttk.Frame(plot_layout)
        chart_frame.pack(side="left", fill="both", expand=True)

        side_panel = ttk.Frame(plot_layout, width=500)
        side_panel.pack(side="right", fill="both", padx=(10, 0))
        side_panel.pack_propagate(False)

        self.fig = Figure(figsize=(14, 7), dpi=100)
        self.ax = self.fig.add_subplot(111)

        self.canvas = FigureCanvasTkAgg(self.fig, master=chart_frame)
        self.canvas.get_tk_widget().pack(fill="both", expand=True)

        self._apply_matplotlib_theme_colors()

        self.plot_help_label = ttk.Label(
            side_panel,
            text=(
                "Подсказка по графику:\n"
                "1. Загрузите данные.\n"
                "2. Выберите объект, показатели и дату(ы).\n"
                "3. Выберите язык перевода (из языков устройства).\n"
                "4. Нажмите 'Получить выборку' (график строится автоматически)."
            ),
            justify="left",
            wraplength=290,
        )
        self.plot_help_label.pack(fill="x", pady=(0, 8))

        legend_frame = ttk.LabelFrame(side_panel, text="Легенда графика", padding=8)
        legend_frame.pack(fill="x", pady=(0, 10))
        self.legend_frame = legend_frame

        self.legend_rows_container = ttk.Frame(self.legend_frame)
        self.legend_rows_container.pack(fill="x")

        changes_frame = ttk.LabelFrame(side_panel, text="Изменения по датам", padding=8)
        changes_frame.pack(fill="both", expand=True, pady=(6, 0))

        self.changes_text = tk.Text(changes_frame, height=36, wrap="word")
        self.changes_text.pack(side="left", fill="both", expand=True)
        self.changes_text.configure(state="disabled")

        changes_scroll = ttk.Scrollbar(changes_frame, orient="vertical", command=self.changes_text.yview)
        changes_scroll.pack(side="right", fill="y")
        self.changes_text.configure(yscrollcommand=changes_scroll.set)

    def create_table_area(self):
        table_frame = ttk.Frame(self.table_container)
        table_frame.pack(fill="both", expand=True)

        self.tree = ttk.Treeview(table_frame, show="headings")
        vsb = ttk.Scrollbar(
            table_frame,
            orient="vertical",
            command=self.tree.yview,
        )
        hsb = ttk.Scrollbar(
            table_frame,
            orient="horizontal",
            command=self.tree.xview,
        )
        self.tree.configure(yscrollcommand=vsb.set, xscrollcommand=hsb.set)

        self.tree.grid(row=0, column=0, sticky="nsew")
        vsb.grid(row=0, column=1, sticky="ns")
        hsb.grid(row=1, column=0, sticky="ew")

        table_frame.rowconfigure(0, weight=1)
        table_frame.columnconfigure(0, weight=1)

    def update_columns_hint(self):
        if self.data is None or self.data.empty:
            self.columns_hint.config(text="Столбцы не определены" if self._is_ru() else "Columns are not detected")
            return

        preview = ", ".join(map(str, self.data.columns[:8]))
        if len(self.data.columns) > 8:
            preview += ", ..."
        params_preview = ", ".join(self.param_columns[:5]) if self.param_columns else "не найдены"
        if len(self.param_columns) > 5:
            params_preview += ", ..."

        if self._is_ru():
            text = (
                f"Найдено столбцов: {len(self.data.columns)} | "
                f"Объект: {self.object_column or 'не найден'} | "
                f"Дата: {self.date_column or 'не найдена'} | "
                f"Показатели: {len(self.param_columns)} ({params_preview}) | "
                f"Первые столбцы: {preview}"
            )
        else:
            text = (
                f"Columns found: {len(self.data.columns)} | "
                f"Object: {self.object_column or 'not found'} | "
                f"Date: {self.date_column or 'not found'} | "
                f"Metrics: {len(self.param_columns)} ({params_preview}) | "
                f"First columns: {preview}"
            )
        self.columns_hint.config(text=text)

    def parse_date(self, value):
        return pd.to_datetime(value, errors="coerce", dayfirst=False)

    def parse_date_filter_text(self, text):
        raw = (text or "").strip()
        if not raw:
            return None, None

        if "," in raw:
            parts = [part.strip() for part in raw.split(",") if part.strip()]
            parsed_dates = pd.to_datetime(parts, errors="coerce", dayfirst=True)
            parsed_dates = parsed_dates[~pd.isna(parsed_dates)]
            return ("list", parsed_dates) if len(parsed_dates) else ("invalid_list", parts)

        range_match = re.fullmatch(
            r"\s*(\d{1,2}[./-]\d{1,2}[./-]\d{2,4})\s*[-\u2013\u2014]\s*(\d{1,2}[./-]\d{1,2}[./-]\d{2,4})\s*",
            raw,
        )
        if range_match:
            date_from = self.parse_date(range_match.group(1))
            date_to = self.parse_date(range_match.group(2))
            if pd.isna(date_from) or pd.isna(date_to):
                return "invalid_range", raw
            if date_from > date_to:
                date_from, date_to = date_to, date_from
            return "range", (date_from, date_to)

        single_date = self.parse_date(raw)
        if pd.isna(single_date):
            return "invalid_single", raw
        return "single", single_date

    def get_filtered_dataframe(self):
        if self.data is None or self.data.empty:
            self._show_warning("Внимание", "Attention", "Сначала загрузите данные!", "Load data first!")
            return None

        df = self.data.copy()

        obj_value = self.obj_entry.get().strip()
        if hasattr(self, "obj_combo"):
            combo_value = self.obj_combo.get().strip()
            if combo_value:
                obj_value = combo_value
        if obj_value:
            if self.object_column and self.object_column in df.columns:
                mask = df[self.object_column].astype(str).str.contains(obj_value, case=False, na=False)
                df = df[mask]
            else:
                self._show_warning("Нет столбца", "Missing column", "Столбец объекта не найден.", "Object column was not found.")
                return None

        param_text = self.param_entry.get().strip()
        if param_text:
            requested = [p.strip() for p in param_text.split(",") if p.strip()]
            col_map = {str(col).lower(): col for col in df.columns}
            selected_cols = []

            for item in requested:
                match = col_map.get(item.lower())
                if match:
                    selected_cols.append(match)

            if not selected_cols:
                self._show_warning(
                    "Нет показателей",
                    "No metrics",
                    "Ни один из указанных показателей не найден.",
                    "None of the specified metrics were found.",
                )
                return None

            keep_cols = []
            for extra_col in [self.object_column, self.date_column, "__source_file__"]:
                if extra_col and extra_col in df.columns and extra_col not in keep_cols:
                    keep_cols.append(extra_col)

            for col in selected_cols:
                if col not in keep_cols:
                    keep_cols.append(col)

            df = df[keep_cols]

        if self.date_column and self.date_column in df.columns:
            df[self.date_column] = pd.to_datetime(df[self.date_column], errors="coerce")
            date_filter_text = self.date_entry.get().strip()
            filter_mode, filter_value = self.parse_date_filter_text(date_filter_text)

            if filter_mode == "list":
                df = df[df[self.date_column].isin(filter_value)]
            elif filter_mode == "range":
                date_from, date_to = filter_value
                df = df[(df[self.date_column] >= date_from) & (df[self.date_column] <= date_to)]
            elif filter_mode == "single":
                df = df[df[self.date_column] == filter_value]
            elif filter_mode == "invalid_list":
                self._show_warning(
                    "Ошибка даты",
                    "Date error",
                    "Некорректный список дат. Используй формат вроде:\n01.01.2026, 05.01.2026, 10.01.2026",
                    "Invalid date list. Use format like:\n01.01.2026, 05.01.2026, 10.01.2026",
                )
                return None
            elif filter_mode == "invalid_range":
                self._show_warning(
                    "Ошибка даты",
                    "Date error",
                    "Некорректный диапазон дат. Используй формат:\n01.01.2026 - 31.01.2026",
                    "Invalid date range. Use format:\n01.01.2026 - 31.01.2026",
                )
                return None
            elif filter_mode == "invalid_single":
                self._show_warning("Ошибка даты", "Date error", "Некорректно задана дата.", "Invalid date value.")
                return None

        if df.empty:
            self._show_warning("Нет данных", "No data", "После фильтрации данных не осталось.", "No data left after filtering.")
            return None

        return df

    def get_selection_and_update(self):
        filtered_df = self.get_filtered_dataframe()
        if filtered_df is not None:
            self.filtered_data = filtered_df
            self.update_table(filtered_df)
            self.update_status(
                f"Выборка готова: {len(filtered_df)} строк"
                if self._is_ru()
                else f"Selection is ready: {len(filtered_df)} rows"
            )
            self._render_plot()

    def _render_plot(self):
        if self.filtered_data is None or self.filtered_data.empty:
            self._show_warning("Внимание", "Attention", "Сначала получите выборку!", "Build selection first!")
            return

        self.ax.clear()
        df_plot = self.filtered_data.copy()

        if self.date_column and self.date_column in df_plot.columns:
            df_plot[self.date_column] = pd.to_datetime(df_plot[self.date_column], errors="coerce")

        numeric_cols = df_plot.select_dtypes(include=["number"]).columns.tolist()
        if not numeric_cols:
            self._show_warning(
                "Нет данных",
                "No data",
                "В выборке нет числовых показателей для графика.",
                "No numeric metrics in selection for chart.",
            )
            return

        if self.theme_mode == "dark":
            palette = [
                "#ff6b6b", "#4dd0e1", "#ffd54f", "#ab47bc", "#81c784",
                "#64b5f6", "#ff8a65", "#ba68c8", "#fff176", "#f06292",
            ]
        else:
            palette = [
                "#d62728", "#1f77b4", "#2ca02c", "#9467bd", "#ff7f0e",
                "#17becf", "#8c564b", "#bcbd22", "#e377c2", "#7f7f7f",
            ]
        self.ax.set_prop_cycle(color=palette)

        use_date_axis = self.date_column and self.date_column in df_plot.columns
        if use_date_axis:
            df_plot = df_plot.sort_values(self.date_column).dropna(subset=[self.date_column])
            x_vals = df_plot[self.date_column]

            for col in numeric_cols:
                valid_mask = ~df_plot[col].isna()
                if valid_mask.any():
                    self.ax.plot(
                        x_vals[valid_mask],
                        df_plot.loc[valid_mask, col],
                        marker="o",
                        linewidth=2.4,
                        markersize=4.5,
                        markeredgewidth=0.7,
                        markeredgecolor="#111111" if self.theme_mode == "light" else "#f0f0f0",
                        alpha=0.98,
                        label=str(col),
                    )
            self.ax.set_xlabel("Дата" if self._is_ru() else "Date")
        else:
            for col in numeric_cols:
                series = df_plot[col].dropna().reset_index(drop=True)
                if not series.empty:
                    self.ax.plot(
                        range(len(series)),
                        series,
                        marker="o",
                        linewidth=2.4,
                        markersize=4.5,
                        markeredgewidth=0.7,
                        markeredgecolor="#111111" if self.theme_mode == "light" else "#f0f0f0",
                        alpha=0.98,
                        label=str(col),
                    )
            self.ax.set_xlabel("Индекс строки" if self._is_ru() else "Row index")

        if use_date_axis:
            x_numeric = mdates.date2num(pd.to_datetime(df_plot[self.date_column]).dt.to_pydatetime())
        else:
            x_numeric = np.arange(len(df_plot), dtype=float)
        self._draw_overlap_segments(df_plot, numeric_cols, x_numeric)

        self.ax.set_ylabel("Значение" if self._is_ru() else "Value")
        self.ax.set_title("График показателей" if self._is_ru() else "Metrics chart")
        self.ax.grid(True, alpha=0.3)
        self._render_legend()

        try:
            plt.setp(self.ax.get_xticklabels(), rotation=45, ha="right")
        except Exception:
            pass

        self.fig.tight_layout()
        self.canvas.draw()
        self.update_changes_summary(df_plot)
        self._apply_matplotlib_theme_colors()
        self.update_status("График обновлен" if self._is_ru() else "Chart updated")

    def _draw_overlap_segments(self, df_plot, numeric_cols, x_numeric):
        if df_plot is None or df_plot.empty or len(df_plot) < 2:
            return

        line_colors = {}
        for ln in self.ax.get_lines():
            label = str(ln.get_label())
            if label in numeric_cols:
                line_colors[label] = ln.get_color()

        y_min, y_max = self.ax.get_ylim()
        y_span = max(1e-9, float(y_max - y_min))
        offset_step = y_span * 0.004

        segments = []
        colors = []
        widths = []

        for i in range(1, len(df_plot)):
            groups = {}
            for col in numeric_cols:
                y1 = df_plot[col].iloc[i - 1]
                y2 = df_plot[col].iloc[i]
                if pd.isna(y1) or pd.isna(y2):
                    continue
                key = (round(float(y1), 8), round(float(y2), 8))
                groups.setdefault(key, []).append(col)

            for (y1, y2), cols in groups.items():
                if len(cols) < 2:
                    continue
                x1 = float(x_numeric[i - 1])
                x2 = float(x_numeric[i])
                half = (len(cols) - 1) / 2.0
                for idx, col in enumerate(cols):
                    y_shift = (idx - half) * offset_step
                    segments.append([(x1, y1 + y_shift), (x2, y2 + y_shift)])
                    colors.append(line_colors.get(col, "#ffffff"))
                    widths.append(2.8)

        if not segments:
            return

        collection = LineCollection(segments, colors=colors, linewidths=widths, capstyle="round", zorder=6)
        self.ax.add_collection(collection)

    def update_table(self, df):
        self.clear_table()

        preview_df = df.head(200).copy()
        preview_df = preview_df.fillna("")

        columns = [self._translate_data_text(col) for col in preview_df.columns]
        self.tree["columns"] = columns

        for col in columns:
            self.tree.heading(col, text=col, anchor="w")
            self.tree.column(col, width=140, anchor="w")

        for _, row in preview_df.iterrows():
            self.tree.insert("", "end", values=[self._translate_data_text(v) for v in row.tolist()])

    def clear_table(self):
        self.tree.delete(*self.tree.get_children())
        self.tree["columns"] = ()

    def clear_plot(self):
        self.ax.clear()
        self.ax.set_title("")
        self._clear_legend()
        self._apply_matplotlib_theme_colors()
        self.canvas.draw()
        self.update_changes_text(
            "Изменения появятся после построения графика.\n\n"
            "Будут показаны общее изменение по каждому показателю и даты, когда происходили изменения."
            if self._is_ru()
            else
            "Changes will appear after chart rendering.\n\n"
            "You will see total change per metric and dates when changes happened."
        )

    def clear_filters(self):
        self.obj_entry.delete(0, "end")
        self.param_entry.delete(0, "end")
        self.date_entry.delete(0, "end")
        self.filtered_data = None
        self.clear_table()
        self.clear_plot()
        self.update_status("Фильтры очищены" if self._is_ru() else "Filters cleared")

    def update_status(self, text):
        self.status_var.set(text)

    def _bind_zoom_shortcuts(self):
        self._cache_base_fonts()
        self.root.bind_all("<Control-MouseWheel>", self._on_ctrl_mousewheel)
        self.root.bind_all("<Control-Button-4>", self._on_ctrl_mousewheel_linux)
        self.root.bind_all("<Control-Button-5>", self._on_ctrl_mousewheel_linux)

    def _cache_base_fonts(self):
        for name in ("TkDefaultFont", "TkTextFont", "TkMenuFont", "TkHeadingFont", "TkCaptionFont", "TkSmallCaptionFont", "TkIconFont"):
            try:
                f = tkfont.nametofont(name)
                self.base_font_sizes[name] = int(f.cget("size"))
            except Exception:
                continue

    def _set_ui_scale(self, scale):
        new_scale = max(0.8, min(1.8, scale))
        if abs(new_scale - self.ui_scale) < 1e-6:
            return
        self.ui_scale = new_scale
        try:
            self.root.tk.call("tk", "scaling", self.ui_scale)
        except Exception:
            pass

        if self.base_font_sizes:
            for name, base_size in self.base_font_sizes.items():
                try:
                    f = tkfont.nametofont(name)
                    sign = -1 if base_size < 0 else 1
                    sized = max(7, int(round(abs(base_size) * self.ui_scale)))
                    f.configure(size=sign * sized)
                except Exception:
                    continue

        self._apply_matplotlib_theme_colors()
        try:
            self.canvas.draw()
        except Exception:
            pass
        self.update_status(
            f"Масштаб интерфейса: {int(self.ui_scale * 100)}%"
            if self._is_ru()
            else f"UI scale: {int(self.ui_scale * 100)}%"
        )

    def _on_ctrl_mousewheel(self, event):
        delta = 1 if event.delta > 0 else -1
        step = 0.08
        self._set_ui_scale(self.ui_scale + delta * step)
        return "break"

    def _on_ctrl_mousewheel_linux(self, event):
        delta = 1 if getattr(event, "num", 0) == 4 else -1
        step = 0.08
        self._set_ui_scale(self.ui_scale + delta * step)
        return "break"

    def _toggle_theme(self):
        self.theme_mode = "dark" if self.theme_mode == "light" else "light"
        if hasattr(self, "theme_toggle_btn"):
            self.theme_toggle_btn.config(text="☾" if self.theme_mode == "dark" else "☀")
        self._apply_theme()
        # On Windows some ttk widgets (especially Combobox popup/list) repaint with a delay.
        # Re-apply after idle so the first toggle is fully consistent.
        self.root.after_idle(self._apply_theme)
        try:
            self.canvas.draw()
        except Exception:
            pass

    def _apply_theme(self):
        # Basic light/dark palette for ttk + tk widgets.
        if self.theme_mode == "dark":
            bg_root = "#1e1e1e"
            fg = "#e6e6e6"
            frame_bg = "#262626"
            panel_bg = "#2a2a2a"
            border = "#4a4a4a"
            btn_bg = "#111111"
            btn_active = "#1f1f1f"
            text_bg = "#2b2b2b"
            tree_bg = "#2a2a2a"
            tree_header_bg = "#1c1c1c"
            select_bg = "#505050"
        else:
            bg_root = "#f5f5f5"
            fg = "#111111"
            frame_bg = "#ffffff"
            panel_bg = "#ffffff"
            border = "#cfcfcf"
            btn_bg = "#eaeaea"
            btn_active = "#dcdcdc"
            text_bg = "#ffffff"
            tree_bg = "#ffffff"
            tree_header_bg = "#f0f0f0"
            select_bg = "#d9e8ff"

        try:
            self.root.configure(bg=bg_root)
        except Exception:
            pass

        # ttk themes are limited; use explicit style overrides.
        self.style.configure("TFrame", background=frame_bg)
        self.style.configure("TPanedwindow", background=frame_bg, borderwidth=0, sashwidth=8)
        self.style.configure("Sash", background=border)
        self.style.configure("TLabelframe", background=panel_bg, foreground=fg, bordercolor=border)
        self.style.configure("TLabelframe.Label", background=panel_bg, foreground=fg)
        self.style.configure("TLabel", background=panel_bg, foreground=fg)
        self.style.configure("PlotSide.TLabel", background=panel_bg, foreground=fg)
        self.style.configure(
            "App.TButton",
            background=btn_bg,
            foreground=fg,
            bordercolor=border,
            lightcolor=btn_bg,
            darkcolor=btn_bg,
            relief="solid",
            borderwidth=1,
            focusthickness=0,
        )
        self.style.map(
            "App.TButton",
            background=[("active", btn_active), ("pressed", btn_active), ("disabled", frame_bg)],
            foreground=[("disabled", "#8c8c8c"), ("!disabled", fg)],
            bordercolor=[("active", border), ("pressed", border), ("!disabled", border)],
        )
        self.style.configure(
            "TEntry",
            fieldbackground=text_bg,
            foreground=fg,
            insertcolor=fg,
            bordercolor=border,
            lightcolor=text_bg,
            darkcolor=text_bg,
        )
        self.style.configure(
            "App.TCombobox",
            fieldbackground=text_bg,
            foreground=fg,
            background=btn_bg,
            arrowcolor=fg,
            bordercolor=border,
            lightcolor=text_bg,
            darkcolor=text_bg,
        )
        self.style.map(
            "App.TCombobox",
            fieldbackground=[("readonly", text_bg), ("!disabled", text_bg)],
            foreground=[("readonly", fg), ("!disabled", fg)],
            background=[("readonly", btn_bg), ("active", btn_active), ("!disabled", btn_bg)],
            arrowcolor=[("disabled", "#8c8c8c"), ("!disabled", fg)],
        )
        self.style.configure(
            "Treeview",
            background=tree_bg,
            fieldbackground=tree_bg,
            foreground=fg,
            bordercolor=border,
            rowheight=24,
        )
        self.style.map("Treeview", background=[("selected", select_bg)], foreground=[("selected", fg)])
        self.style.configure(
            "Treeview.Heading",
            background=tree_header_bg,
            foreground=fg,
            bordercolor=border,
            lightcolor=tree_header_bg,
            darkcolor=tree_header_bg,
            relief="flat",
        )
        self.style.map("Treeview.Heading", background=[("active", btn_active)])
        self.style.configure(
            "TScrollbar",
            background=btn_bg,
            troughcolor="#1f1f1f" if self.theme_mode == "dark" else panel_bg,
            bordercolor=border,
            arrowcolor=fg,
            gripcount=0,
            relief="flat",
            width=14,
        )
        self.style.map(
            "TScrollbar",
            background=[("active", btn_active), ("pressed", btn_active)],
            arrowcolor=[("disabled", "#8c8c8c"), ("!disabled", fg)],
        )

        # tk.Text (changes panel)
        if hasattr(self, "changes_text"):
            self.changes_text.configure(bg=text_bg, fg=fg, insertbackground=fg)
        if hasattr(self, "plot_help_label"):
            self.plot_help_label.configure(style="PlotSide.TLabel")
        # Combobox dropdown list colors.
        try:
            self.root.option_add("*TCombobox*Listbox.background", text_bg)
            self.root.option_add("*TCombobox*Listbox.foreground", fg)
            self.root.option_add("*TCombobox*Listbox.selectBackground", select_bg)
            self.root.option_add("*TCombobox*Listbox.selectForeground", fg)
        except Exception:
            pass

        # tk.Listbox suggestions may be open; ignore if absent.
        self._apply_matplotlib_theme_colors()
        self._apply_button_style_recursively()

    def _apply_button_style_recursively(self):
        def walk(widget):
            for child in widget.winfo_children():
                if isinstance(child, ttk.Button):
                    try:
                        child.configure(style="App.TButton")
                    except Exception:
                        pass
                walk(child)

        try:
            walk(self.root)
        except Exception:
            pass

    def _apply_matplotlib_theme_colors(self):
        # Keep matplotlib readable for both themes.
        if getattr(self, "fig", None) is None or getattr(self, "ax", None) is None:
            return

        if self.theme_mode == "dark":
            bg = "#1e1e1e"
            fg = "#e6e6e6"
            grid = "#4b4b4b"
        else:
            bg = "white"
            fg = "#111111"
            grid = "#d0d0d0"

        self.fig.patch.set_facecolor(bg)
        self.ax.set_facecolor(bg)

        self.ax.tick_params(colors=fg)
        self.ax.xaxis.label.set_color(fg)
        self.ax.yaxis.label.set_color(fg)
        self.ax.title.set_color(fg)
        self.ax.grid(True, color=grid, alpha=0.35)
        try:
            for spine in self.ax.spines.values():
                spine.set_color(fg)
        except Exception:
            pass

    def _clear_legend(self):
        if not hasattr(self, "legend_rows_container"):
            return
        for w in self.legend_rows_container.winfo_children():
            try:
                w.destroy()
            except Exception:
                pass

    def _render_legend(self):
        self._clear_legend()
        if not hasattr(self, "legend_rows_container"):
            return

        plotted = [ln for ln in self.ax.get_lines() if getattr(ln, "get_label", None)]
        if not plotted:
            return

        # В легенду попадут только линии с явной подписью.
        rows = 0
        for ln in plotted:
            label = ln.get_label()
            if not label or label == "_nolegend_":
                continue
            color = ln.get_color()
            row = ttk.Frame(self.legend_rows_container)
            row.pack(fill="x", pady=2)

            color_box = tk.Label(row, text="  ", bg=color, width=3)
            color_box.pack(side="left", padx=(0, 8))

            ttk.Label(row, text=str(label), style="PlotSide.TLabel").pack(side="left")
            rows += 1

        if rows == 0:
            ttk.Label(self.legend_rows_container, text="Линии не построены.", style="PlotSide.TLabel").pack(anchor="w")

    def update_changes_text(self, text):
        if not hasattr(self, "changes_text"):
            return
        self.changes_text.configure(state="normal")
        self.changes_text.delete("1.0", "end")
        self.changes_text.insert("1.0", text)
        self.changes_text.configure(state="disabled")

    def update_changes_summary(self, df):
        if df is None or df.empty:
            self.update_changes_text("Нет данных для расчета изменений.")
            return

        numeric_cols = df.select_dtypes(include=["number"]).columns.tolist()
        if not numeric_cols:
            self.update_changes_text("Нет числовых показателей для расчета изменений.")
            return

        work = df.copy()
        date_col = self.date_column if self.date_column in work.columns else None
        if date_col:
            work[date_col] = pd.to_datetime(work[date_col], errors="coerce", dayfirst=True)
            work = work.dropna(subset=[date_col]).sort_values(date_col)

        lines = []
        for col in numeric_cols:
            series = pd.to_numeric(work[col], errors="coerce")
            valid = series.dropna()
            if valid.empty:
                continue

            total_change = valid.iloc[-1] - valid.iloc[0]
            lines.append(f"{col}")
            lines.append(f"Общее изменение: {total_change:,.2f}".replace(",", " ").replace(".", ","))

            if date_col and len(work) > 1:
                delta_series = series.diff()
                change_rows = work.loc[delta_series.fillna(0) != 0, [date_col]].copy()
                change_rows["_delta_"] = delta_series[delta_series.fillna(0) != 0]

                if not change_rows.empty:
                    lines.append("Даты изменений:")
                    for _, row in change_rows.head(10).iterrows():
                        date_text = row[date_col].strftime("%d.%m.%Y")
                        delta_text = f"{row['_delta_']:,.2f}".replace(",", " ").replace(".", ",")
                        lines.append(f"- {date_text}: {delta_text}")
                else:
                    lines.append("Даты изменений: изменений не найдено")
            lines.append("")

        if not lines:
            lines = ["Недостаточно данных для расчета изменений."]

        self.update_changes_text("\n".join(lines).strip())

    def export_to_excel(self):
        if self.filtered_data is None or self.filtered_data.empty:
            self._show_warning("Внимание", "Attention", "Сначала получите выборку!", "Build selection first!")
            return

        file_path = filedialog.asksaveasfilename(
            defaultextension=".xlsx",
            filetypes=[("Excel files", "*.xlsx"), ("All files", "*.*")],
        )
        if not file_path:
            return

        try:
            with pd.ExcelWriter(file_path, engine="openpyxl") as writer:
                sheet_name = "Выборка"
                self.filtered_data.to_excel(writer, index=False, sheet_name=sheet_name)
                worksheet = writer.sheets[sheet_name]

                for idx, col in enumerate(self.filtered_data.columns, start=1):
                    col_name = str(col)
                    values = self.filtered_data[col].fillna("").astype(str)
                    max_value_len = values.map(len).max() if not values.empty else 0
                    max_len = max(len(col_name), int(max_value_len))
                    width = min(max_len + 2, 80)
                    col_letter = chr(64 + idx) if idx <= 26 else None
                    if col_letter is None:
                        n = idx
                        letters = []
                        while n > 0:
                            n, rem = divmod(n - 1, 26)
                            letters.append(chr(65 + rem))
                        col_letter = "".join(reversed(letters))
                    worksheet.column_dimensions[col_letter].width = width

            self.update_status(
                f"Экспортировано строк: {len(self.filtered_data)}"
                if self._is_ru()
                else f"Exported rows: {len(self.filtered_data)}"
            )
            self._show_info(
                "Успех",
                "Success",
                f"Данные успешно экспортированы в:\n{file_path}",
                f"Data exported successfully to:\n{file_path}",
            )
        except Exception as e:
            self._show_error("Ошибка", "Error", f"Не удалось экспортировать данные:\n{e}", f"Failed to export data:\n{e}")


AUTO_GROUP_ENABLED = True
AUTO_GROUP_MAX_GROUP_COLS = 3
AUTO_GROUP_MAX_UNIQUE = 50
AUTO_GROUP_UNIQUE_FRAC = 0.20
AUTO_GROUP_AGG = "mean"

OBJECT_PICKER_ENABLED = True
OBJECT_PICKER_MAX_ITEMS = 5000

HINT_OBJECT_EXAMPLES = 8
HINT_PARAMS_EXAMPLES = 12


def _extract_object_values(df, object_col):
    if df is None or df.empty:
        return []

    target_col = object_col
    if not target_col or target_col not in df.columns:
        candidates = []
        for col in df.columns:
            if col == "__source_file__":
                continue
            if is_numeric_dtype(df[col]):
                continue
            nunq = df[col].nunique(dropna=True)
            if 1 < nunq <= 5000:
                candidates.append((nunq, col))
        if not candidates:
            return []
        candidates.sort(key=lambda x: x[0])
        target_col = candidates[0][1]

    s = df[target_col].dropna().astype(str).str.strip()
    s = s[s != ""].drop_duplicates()
    vals = sorted(s.tolist())
    if len(vals) > OBJECT_PICKER_MAX_ITEMS:
        vals = vals[:OBJECT_PICKER_MAX_ITEMS]
    return vals


def _get_object_examples(df, object_col, limit=HINT_OBJECT_EXAMPLES):
    if df is None or df.empty or not object_col or object_col not in df.columns:
        return []
    s = df[object_col].dropna().astype(str).str.strip()
    s = s[s != ""].drop_duplicates()
    return s.head(limit).tolist()


def _get_numeric_param_cols(df):
    if df is None or df.empty:
        return []
    cols = []
    for c in df.columns:
        if c in ("__source_file__",):
            continue
        if _date_parse_ratio(df[c]) >= 0.6:
            continue
        if is_numeric_dtype(df[c]) or _coerce_numeric_ratio(df[c]) >= 0.85:
            cols.append(str(c))
    return cols


def _auto_detect_group_cols(df, object_col=None, date_col=None):
    if df is None or df.empty:
        return [], df

    work = df.copy()

    group_cols = []
    if object_col and object_col in work.columns:
        group_cols.append(object_col)

    if date_col and date_col in work.columns:
        work[date_col] = pd.to_datetime(work[date_col], errors="coerce").dt.date
        group_cols.append(date_col)

    n = len(work)
    for col in work.columns:
        if col in group_cols:
            continue
        if col == "__source_file__":
            continue
        if is_numeric_dtype(work[col]):
            continue

        nunq = work[col].nunique(dropna=True)
        if nunq <= min(AUTO_GROUP_MAX_UNIQUE, max(2, int(n * AUTO_GROUP_UNIQUE_FRAC))):
            group_cols.append(col)
            if len(group_cols) >= AUTO_GROUP_MAX_GROUP_COLS:
                break

    return group_cols, work


def _group_and_aggregate(df, group_cols, agg=AUTO_GROUP_AGG):
    if df is None or df.empty or not group_cols:
        return df

    numeric_cols = [c for c in df.columns if is_numeric_dtype(df[c]) and c not in group_cols]
    if not numeric_cols:
        return df[group_cols].drop_duplicates().reset_index(drop=True)

    agg_map = {c: agg for c in numeric_cols}
    out = df.groupby(group_cols, dropna=False, as_index=False).agg(agg_map)
    return out


def _refresh_object_picker(self):
    if not OBJECT_PICKER_ENABLED:
        return
    if not hasattr(self, "obj_combo"):
        return
    self.obj_combo["values"] = _extract_object_values(self.data, self.object_column)


def _refresh_hints(self):
    if getattr(self, "data", None) is None or self.data is None or self.data.empty:
        return

    if hasattr(self, "object_help_label"):
        if self.object_column and self.object_column in self.data.columns:
            examples = _get_object_examples(self.data, self.object_column)
            ex_text = ", ".join(examples) if examples else "нет примеров"
            if self._is_ru():
                self.object_help_label.config(
                    text=f"Объект: фильтр по столбцу '{self.object_column}'. Примеры: {ex_text}"
                )
            else:
                self.object_help_label.config(
                    text=f"Object: filter by column '{self.object_column}'. Examples: {ex_text}"
                )
        else:
            self.object_help_label.config(
                text="Объект: столбец не определен (переименуйте колонку в CSV, например 'Объект'/'Код')."
                if self._is_ru()
                else "Object: column is not detected (rename CSV column, for example 'Object'/'Code')."
            )

    if hasattr(self, "param_help_label"):
        numeric_cols = _get_numeric_param_cols(self.data)
        preview = ", ".join(numeric_cols[:HINT_PARAMS_EXAMPLES]) + (
            " ..." if len(numeric_cols) > HINT_PARAMS_EXAMPLES else ""
        )
        if numeric_cols:
            self.param_help_label.config(
                text=f"Параметры: вводите названия числовых столбцов через запятую. Доступно: {preview}"
                if self._is_ru()
                else f"Metrics: enter numeric column names separated by commas. Available: {preview}"
            )
        else:
            self.param_help_label.config(
                text="Параметры: числовые столбцы не найдены."
                if self._is_ru()
                else "Metrics: numeric columns were not found."
            )

    # If user has not typed parameters yet, suggest detected parameters automatically.
    if hasattr(self, "param_entry"):
        current_value = self.param_entry.get().strip()
        if not current_value and getattr(self, "param_columns", None):
            auto_value = ", ".join(self.param_columns[:HINT_PARAMS_EXAMPLES])
            self.param_entry.insert(0, auto_value)


def _refresh_date_suggestions(self):
    self.available_dates = []
    if getattr(self, "data", None) is None or self.data is None or self.data.empty:
        return
    if not self.date_column or self.date_column not in self.data.columns:
        return

    parsed = pd.to_datetime(self.data[self.date_column], errors="coerce", dayfirst=True)
    parsed = parsed.dropna().dt.strftime("%d.%m.%Y").drop_duplicates()
    self.available_dates = sorted(parsed.tolist())


def _hide_date_suggest_popup(self):
    popup = getattr(self, "_date_suggest_popup", None)
    if popup is not None:
        try:
            popup.destroy()
        except Exception:
            pass
        self._date_suggest_popup = None
        self._date_suggest_entry = None


def _choose_date_suggestion(self, entry):
    popup = getattr(self, "_date_suggest_popup", None)
    if popup is None:
        return
    listbox = getattr(self, "_date_suggest_listbox", None)
    if listbox is None:
        return
    selection = listbox.curselection()
    if not selection:
        return
    value = listbox.get(selection[0])
    entry.delete(0, "end")
    entry.insert(0, value)
    _hide_date_suggest_popup(self)


def _show_date_suggestions_for_entry(self, entry):
    text = entry.get().strip()
    if not text or len(text) < 1:
        _hide_date_suggest_popup(self)
        return

    all_dates = getattr(self, "available_dates", [])
    if not all_dates:
        _hide_date_suggest_popup(self)
        return

    suggestions = [d for d in all_dates if text in d][:15]
    if not suggestions:
        _hide_date_suggest_popup(self)
        return

    popup = getattr(self, "_date_suggest_popup", None)
    same_entry = getattr(self, "_date_suggest_entry", None) is entry
    if popup is None or not same_entry:
        _hide_date_suggest_popup(self)
        popup = tk.Toplevel(self.root)
        popup.overrideredirect(True)
        popup.transient(self.root)
        self._date_suggest_popup = popup
        self._date_suggest_entry = entry

        listbox = tk.Listbox(popup, height=8)
        listbox.pack(fill="both", expand=True)
        self._date_suggest_listbox = listbox

        listbox.bind("<Double-Button-1>", lambda _e: _choose_date_suggestion(self, entry))
        listbox.bind("<Return>", lambda _e: _choose_date_suggestion(self, entry))
        listbox.bind("<Escape>", lambda _e: _hide_date_suggest_popup(self))
    else:
        listbox = self._date_suggest_listbox

    listbox.delete(0, "end")
    for item in suggestions:
        listbox.insert("end", item)

    x = entry.winfo_rootx()
    y = entry.winfo_rooty() + entry.winfo_height() + 2
    w = max(entry.winfo_width(), 130)
    popup.geometry(f"{w}x160+{x}+{y}")


def _open_calendar_for_entry(self, entry):
    if Calendar is None:
        if self._is_ru():
            messagebox.showinfo(
                "Календарь недоступен",
                "Для выбора даты календарем установите пакет: pip install tkcalendar",
            )
        else:
            messagebox.showinfo(
                "Calendar unavailable",
                "To pick date with calendar install package: pip install tkcalendar",
            )
        return

    win = tk.Toplevel(self.root)
    win.title("Выберите дату или диапазон" if self._is_ru() else "Choose date or range")
    win.transient(self.root)
    win.grab_set()
    win.configure(bg="#1e1e1e" if self.theme_mode == "dark" else "#f5f5f5")

    current = entry.get().strip()
    filter_mode, filter_value = self.parse_date_filter_text(current)

    if filter_mode == "range":
        parsed_start, parsed_end = filter_value
    elif filter_mode == "single":
        parsed_start = filter_value
        parsed_end = filter_value
    else:
        parsed_start = pd.Timestamp.today()
        parsed_end = pd.Timestamp.today()

    if self.theme_mode == "dark":
        cal_colors = dict(
            background="#2a2a2a",
            foreground="#e6e6e6",
            bordercolor="#4a4a4a",
            headersbackground="#1f1f1f",
            headersforeground="#e6e6e6",
            selectbackground="#505050",
            selectforeground="#ffffff",
            normalbackground="#2a2a2a",
            normalforeground="#e6e6e6",
            weekendbackground="#2a2a2a",
            weekendforeground="#e6e6e6",
        )
    else:
        cal_colors = dict(
            background="#ffffff",
            foreground="#111111",
            bordercolor="#cfcfcf",
            headersbackground="#f0f0f0",
            headersforeground="#111111",
            selectbackground="#d9e8ff",
            selectforeground="#111111",
            normalbackground="#ffffff",
            normalforeground="#111111",
            weekendbackground="#ffffff",
            weekendforeground="#111111",
        )

    info_label = ttk.Label(
        win,
        text=(
            "Слева выбери первую дату, справа вторую. Для одной даты можно нажать левую кнопку выбора."
            if self._is_ru()
            else "Choose first date on the left, second date on the right. For single date use the left button."
        ),
        style="PlotSide.TLabel" if hasattr(self, "plot_help_label") else "TLabel",
        wraplength=620,
        justify="left",
    )
    info_label.pack(fill="x", padx=10, pady=(10, 6))

    calendars = ttk.Frame(win)
    calendars.pack(fill="both", expand=True, padx=10, pady=(0, 10))

    cal_from = Calendar(
        calendars,
        selectmode="day",
        date_pattern="dd.mm.yyyy",
        year=int(parsed_start.year),
        month=int(parsed_start.month),
        day=int(parsed_start.day),
        **cal_colors,
    )
    cal_from.pack(side="left", padx=(0, 10), pady=4)

    cal_to = Calendar(
        calendars,
        selectmode="day",
        date_pattern="dd.mm.yyyy",
        year=int(parsed_end.year),
        month=int(parsed_end.month),
        day=int(parsed_end.day),
        **cal_colors,
    )
    cal_to.pack(side="left", padx=(10, 0), pady=4)

    btns = ttk.Frame(win)
    btns.pack(fill="x", padx=10, pady=(0, 10))

    def _apply_single_date():
        selected = cal_from.get_date()
        entry.delete(0, "end")
        entry.insert(0, selected)
        win.destroy()

    def _apply_range():
        date_from = pd.to_datetime(cal_from.get_date(), errors="coerce", dayfirst=True)
        date_to = pd.to_datetime(cal_to.get_date(), errors="coerce", dayfirst=True)
        if pd.isna(date_from) or pd.isna(date_to):
            return
        if date_from > date_to:
            date_from, date_to = date_to, date_from
        entry.delete(0, "end")
        entry.insert(0, f"{date_from.strftime('%d.%m.%Y')} - {date_to.strftime('%d.%m.%Y')}")
        win.destroy()

    ttk.Button(btns, text="Одна дата" if self._is_ru() else "Single date", command=_apply_single_date).pack(side="left")
    ttk.Button(btns, text="Диапазон" if self._is_ru() else "Range", command=_apply_range).pack(side="left", padx=8)
    ttk.Button(btns, text="Отмена" if self._is_ru() else "Cancel", command=win.destroy).pack(side="right")


if not hasattr(DataAnalyzerApp, "_orig_create_widgets_fixed"):
    DataAnalyzerApp._orig_create_widgets_fixed = DataAnalyzerApp.create_widgets

    def _patched_create_widgets_fixed(self):
        self._orig_create_widgets_fixed()

        top_frame = self.obj_entry.master
        self.obj_entry.grid_remove()
        self.obj_combo = ttk.Combobox(top_frame, style="App.TCombobox")
        self.obj_combo.grid(row=1, column=1, sticky="ew", padx=5, pady=5)
        self.obj_combo.set(self.obj_entry.get())

        def _sync_combo_to_entry(_event=None):
            val = (self.obj_combo.get() or "").strip()
            self.obj_entry.delete(0, "end")
            self.obj_entry.insert(0, val)

        def _sync_entry_to_combo(_event=None):
            try:
                self.obj_combo.set(self.obj_entry.get())
            except Exception:
                pass

        self.obj_combo.bind("<<ComboboxSelected>>", _sync_combo_to_entry)
        self.obj_combo.bind("<KeyRelease>", _sync_combo_to_entry)
        self.obj_entry.bind("<KeyRelease>", _sync_entry_to_combo)

        self.available_dates = []
        self._date_suggest_popup = None
        self._date_suggest_entry = None
        self._date_suggest_listbox = None

        def _bind_date_entry(entry):
            entry.bind("<KeyRelease>", lambda _e, target=entry: _show_date_suggestions_for_entry(self, target))
            entry.bind("<FocusOut>", lambda _e: self.root.after(100, lambda: _hide_date_suggest_popup(self)))
            entry.bind("<Double-Button-1>", lambda _e, target=entry: _open_calendar_for_entry(self, target))

        _bind_date_entry(self.date_entry)

        lang_frame = ttk.Frame(top_frame)
        lang_frame.grid(row=3, column=0, columnspan=5, sticky="ew", pady=(6, 2))
        lang_frame.columnconfigure(1, weight=1)

        ttk.Label(lang_frame, text="Язык перевода:").grid(row=0, column=0, sticky="e", padx=(0, 5))
        self.target_lang_combo = ttk.Combobox(
            lang_frame,
            state="readonly",
            style="App.TCombobox",
            values=self.translation_lang_options,
        )
        self.target_lang_combo.grid(row=0, column=1, sticky="ew")
        self.target_lang_combo.set(self.translation_lang_options[0])
        self.target_lang_combo.bind("<<ComboboxSelected>>", self._on_language_change)

        button_frames = [w for w in top_frame.winfo_children() if isinstance(w, ttk.Frame)]
        if button_frames:
            try:
                button_frames[1].grid_configure(row=4)
            except Exception:
                pass

        self.columns_hint.grid_configure(row=9)

        self.object_help_label = ttk.Label(
            top_frame,
            text="Объект: часть названия/кода (можно вводить не полностью).",
        )
        self.object_help_label.grid(row=5, column=0, columnspan=5, sticky="w", padx=5, pady=(2, 0))

        self.date_help_label = ttk.Label(
            top_frame,
            text="Дата(ы): одна дата, список через запятую или диапазон через '-' . Пример: 01.01.2026 - 31.01.2026",
        )
        self.date_help_label.grid(row=6, column=0, columnspan=5, sticky="w", padx=5, pady=(2, 0))

        self.param_help_label = ttk.Label(
            top_frame,
            text="Параметры: названия числовых столбцов через запятую.",
        )
        self.param_help_label.grid(row=7, column=0, columnspan=5, sticky="w", padx=5, pady=(2, 0))

        self.lang_help_label = ttk.Label(
            top_frame,
            text="Языки: доступны только языки, найденные на устройстве.",
        )
        self.lang_help_label.grid(row=8, column=0, columnspan=5, sticky="w", padx=5, pady=(2, 0))

        def _show_help():
            is_ru = str(getattr(self, "current_language_code", "ru")).startswith("ru")
            obj_col = self.object_column or "не найден"
            date_col = self.date_column or "не найдена"

            numeric_cols = _get_numeric_param_cols(self.data)
            numeric_preview = ", ".join(numeric_cols[:20]) + (" ..." if len(numeric_cols) > 20 else "")
            if not numeric_cols:
                numeric_preview = "числовые столбцы не найдены"

            obj_examples = _get_object_examples(self.data, self.object_column)
            obj_preview = ", ".join(obj_examples) if obj_examples else "нет примеров"
            if self.theme_mode == "dark":
                bg = "#1e1e1e"
                panel = "#2a2a2a"
                fg = "#e6e6e6"
                border = "#4a4a4a"
                accent = "#b8d7ff"
            else:
                bg = "#f5f5f5"
                panel = "#ffffff"
                fg = "#111111"
                border = "#cfcfcf"
                accent = "#1f4f8a"

            help_win = tk.Toplevel(self.root)
            help_win.title("Справка: Объекты и параметры" if is_ru else "Help: Objects and metrics")
            help_win.transient(self.root)
            help_win.grab_set()
            help_win.configure(bg=bg)
            help_win.geometry("760x520")

            outer = tk.Frame(help_win, bg=panel, highlightbackground=border, highlightthickness=1)
            outer.pack(fill="both", expand=True, padx=12, pady=12)

            title = tk.Label(
                outer,
                text="Как пользоваться фильтрами и графиком" if is_ru else "How to use filters and chart",
                bg=panel,
                fg=accent,
                font=("Segoe UI", 11, "bold"),
                anchor="w",
            )
            title.pack(fill="x", padx=12, pady=(10, 6))

            if is_ru:
                help_text = (
                    "Объект — значение из столбца, по которому фильтруются строки.\n"
                    f"Определенный столбец объекта: {obj_col}\n"
                    f"Примеры объектов: {obj_preview}\n\n"
                    "Параметры — числовые столбцы для графика и аналитики.\n"
                    "Вводите названия через запятую, точно как в таблице.\n"
                    f"Доступные параметры: {numeric_preview}\n\n"
                    f"Столбец даты: {date_col}\n"
                    "Можно использовать: одну дату, список дат, или диапазон Дата с/Дата по.\n\n"
                    "Языки:\n"
                    "В поле 'Язык перевода' доступны только языки устройства.\n"
                    f"Текущий язык интерфейса: {self.target_lang_combo.get() if hasattr(self, 'target_lang_combo') else 'не выбран'}\n\n"
                    "Быстрый порядок действий:\n"
                    "1) Загрузите данные.\n"
                    "2) Выберите объект (или часть названия).\n"
                    "3) Укажите параметры.\n"
                    "4) Нажмите 'Получить выборку'.\n"
                    "5) Обновите график или экспортируйте в Excel.\n\n"
                    "Подсказка: если выборка пустая, проверьте формат даты и названия параметров."
                )
            else:
                help_text = (
                    "Object is a value from the object column used to filter rows.\n"
                    f"Detected object column: {obj_col}\n"
                    f"Object examples: {obj_preview}\n\n"
                    "Metrics are numeric columns for charting and analysis.\n"
                    "Enter exact column names separated by commas.\n"
                    f"Available metrics: {numeric_preview}\n\n"
                    f"Date column: {date_col}\n"
                    "You can use a single date, list of dates, or a date range.\n\n"
                    "Languages:\n"
                    "Only device languages are available in the language selector.\n"
                    f"Current interface language: {self.target_lang_combo.get() if hasattr(self, 'target_lang_combo') else 'not selected'}\n\n"
                    "Quick flow:\n"
                    "1) Load data.\n"
                    "2) Select object (full or partial).\n"
                    "3) Set metrics.\n"
                    "4) Click 'Build selection'.\n"
                    "5) Update chart or export to Excel.\n\n"
                    "Tip: if selection is empty, check date format and metric names."
                )

            text_wrap = tk.Text(
                outer,
                wrap="word",
                bg=panel,
                fg=fg,
                insertbackground=fg,
                relief="flat",
                font=("Segoe UI", 10),
                padx=10,
                pady=6,
            )
            text_wrap.pack(fill="both", expand=True, padx=(10, 6), pady=(0, 8), side="left")
            text_wrap.insert("1.0", help_text)
            text_wrap.configure(state="disabled")

            scr = ttk.Scrollbar(outer, orient="vertical", command=text_wrap.yview)
            scr.pack(side="right", fill="y", padx=(0, 8), pady=(0, 8))
            text_wrap.configure(yscrollcommand=scr.set)

            close_btn = ttk.Button(
                outer,
                text="Закрыть" if is_ru else "Close",
                command=help_win.destroy,
                style="App.TButton",
            )
            close_btn.pack(anchor="e", padx=10, pady=(0, 10))

        help_parent = None
        for frame in [w for w in top_frame.winfo_children() if isinstance(w, ttk.Frame)]:
            try:
                child_texts = [child.cget("text") for child in frame.winfo_children() if isinstance(child, ttk.Button)]
            except Exception:
                child_texts = []
            if "Получить выборку" in child_texts or "Build selection" in child_texts:
                help_parent = frame
                break
        if help_parent is None:
            frames = [w for w in top_frame.winfo_children() if isinstance(w, ttk.Frame)]
            help_parent = frames[0] if frames else None
        if help_parent is not None:
            ttk.Button(help_parent, text="Справка", command=_show_help).pack(side="left", padx=5)

    DataAnalyzerApp.create_widgets = _patched_create_widgets_fixed


if not hasattr(DataAnalyzerApp, "_orig_update_columns_hint_fixed"):
    DataAnalyzerApp._orig_update_columns_hint_fixed = DataAnalyzerApp.update_columns_hint

    def _patched_update_columns_hint_fixed(self):
        self._orig_update_columns_hint_fixed()
        _refresh_hints(self)

    DataAnalyzerApp.update_columns_hint = _patched_update_columns_hint_fixed


if not hasattr(DataAnalyzerApp, "_orig_load_single_file_fixed"):
    DataAnalyzerApp._orig_load_single_file_fixed = DataAnalyzerApp.load_single_file

    def _patched_load_single_file_fixed(self):
        self._orig_load_single_file_fixed()
        _refresh_object_picker(self)
        _refresh_date_suggestions(self)
        _refresh_hints(self)

    DataAnalyzerApp.load_single_file = _patched_load_single_file_fixed


if not hasattr(DataAnalyzerApp, "_orig_load_file_from_folder_fixed"):
    DataAnalyzerApp._orig_load_file_from_folder_fixed = DataAnalyzerApp.load_file_from_folder

    def _patched_load_file_from_folder_fixed(self):
        self._orig_load_file_from_folder_fixed()
        _refresh_object_picker(self)
        _refresh_date_suggestions(self)
        _refresh_hints(self)

    DataAnalyzerApp.load_file_from_folder = _patched_load_file_from_folder_fixed


if not hasattr(DataAnalyzerApp, "_orig_get_selection_and_update_fixed"):
    DataAnalyzerApp._orig_get_selection_and_update_fixed = DataAnalyzerApp.get_selection_and_update

    def _patched_get_selection_and_update_fixed(self):
        self._orig_get_selection_and_update_fixed()

        if not AUTO_GROUP_ENABLED:
            return
        if self.filtered_data is None or self.filtered_data.empty:
            return

        group_cols, work = _auto_detect_group_cols(
            self.filtered_data,
            object_col=self.object_column,
            date_col=self.date_column,
        )
        if not group_cols:
            return

        grouped = _group_and_aggregate(work, group_cols, agg=AUTO_GROUP_AGG)
        self.filtered_data = grouped
        self.update_table(grouped)
        self.update_status(
            f"Выборка сгруппирована по: {', '.join(map(str, group_cols))} | строк: {len(grouped)}"
            if self._is_ru()
            else f"Selection grouped by: {', '.join(map(str, group_cols))} | rows: {len(grouped)}"
        )

    DataAnalyzerApp.get_selection_and_update = _patched_get_selection_and_update_fixed


if not hasattr(DataAnalyzerApp, "_orig_clear_filters_fixed"):
    DataAnalyzerApp._orig_clear_filters_fixed = DataAnalyzerApp.clear_filters

    def _patched_clear_filters_fixed(self):
        self._orig_clear_filters_fixed()
        if hasattr(self, "obj_combo"):
            self.obj_combo.set("")

    DataAnalyzerApp.clear_filters = _patched_clear_filters_fixed


if __name__ == "__main__":
    try:
        root = Tk()
        app = DataAnalyzerApp(root)
        root.mainloop()
    except Exception as e:
        try:
            log_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "prisma_error.log")
            with open(log_path, "w", encoding="utf-8") as f:
                f.write("Prisma startup/runtime error\n\n")
                f.write(str(e) + "\n\n")
                f.write(traceback.format_exc())
        except Exception:
            pass
        try:
            messagebox.showerror(
                "Prisma error",
                f"Application failed to start.\n\nError: {e}\n\nSee prisma_error.log near the app.",
            )
        except Exception:
            pass
