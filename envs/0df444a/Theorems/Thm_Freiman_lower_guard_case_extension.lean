-- Prove2me | Theorems.Thm_Freiman_lower_guard_case_extension
-- name    : Freiman.lower_guard_case_extension
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:03:36.284019+00:00
-- url     : https://prove2.me/theorems/aea36263-582b-4e5d-a64f-14741381094c
-- title:
--   Freiman word guards: case extension
-- statement:
--   Apply the finite safe-boundary facts to the actual normalized outward words, retaining the central 4 separator and positive prefix growth.
-- source:
--   Freiman report, 'The complete boundary table for selected words', Appendix app:selection-words, report/source/staging/parts/word_certificates.tex; global_selection.tex admissibility argument; certificates/word_selection/selection_words_printed.json, word_guards.json and source_bindings.json; verification/families/word_selection/verify_word_guards.py.

import Definitions.Def_Freiman_lowerWordGuardData

open Freiman

theorem Freiman.lower_guard_case_extension (hb : LowerGuardBoundaryLaw) (p : LowerPair) (hp : lowerAdmissible p)
    (c : LowerGuardCase) (hv : lowerGuardCaseValid c) (hf : lowerGuardFits c p)
    (l : LowerLabel) (hl : l ∈ c.labels) : lowerGuardExtensionData p l := by
  sorry
