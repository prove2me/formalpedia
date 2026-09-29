-- Prove2me | Theorems.Thm_Freiman_lower_guard_selected_extension
-- name    : Freiman.lower_guard_selected_extension
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:03:55.727987+00:00
-- url     : https://prove2.me/theorems/ed123fdb-b6cd-41bc-8ae3-1879ee162f90
-- title:
--   Freiman word guards: selected extension
-- statement:
--   Apply checked finite cases or the guarded repeated-3 continuation.
-- source:
--   Freiman report, 'The complete boundary table for selected words', Appendix app:selection-words, report/source/staging/parts/word_certificates.tex; global_selection.tex admissibility argument; certificates/word_selection/selection_words_printed.json, word_guards.json and source_bindings.json; verification/families/word_selection/verify_word_guards.py.

import Definitions.Def_Freiman_lowerWordGuardData

open Freiman

theorem Freiman.lower_guard_selected_extension (p : LowerPair) (hp : lowerAdmissible p) (l : LowerLabel) (hl : lowerOffered p l) : lowerGuardExtensionData p l := by
  sorry
