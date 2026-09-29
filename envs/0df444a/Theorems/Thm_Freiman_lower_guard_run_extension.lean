-- Prove2me | Theorems.Thm_Freiman_lower_guard_run_extension
-- name    : Freiman.lower_guard_run_extension
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:03:40.583325+00:00
-- url     : https://prove2.me/theorems/2a06b40c-902d-4df0-b598-8dc4d68ef855
-- title:
--   Freiman word guards: run extension
-- statement:
--   Under both unshortened guards, a repeated run of at least three 3s creates no forbidden boundary, extends both words and ends in 33.
-- source:
--   Freiman report, 'The complete boundary table for selected words', Appendix app:selection-words, report/source/staging/parts/word_certificates.tex; global_selection.tex admissibility argument; certificates/word_selection/selection_words_printed.json, word_guards.json and source_bindings.json; verification/families/word_selection/verify_word_guards.py.

import Definitions.Def_Freiman_lowerWordGuardData

open Freiman

theorem Freiman.lower_guard_run_extension (p : LowerPair) (hp : lowerAdmissible p) (hr : lowerRunOffered p) (k : ℕ) (hk : 3 ≤ k) :
    lowerGuardExtensionData p (List.replicate k 3,List.replicate k 3) := by
  sorry
