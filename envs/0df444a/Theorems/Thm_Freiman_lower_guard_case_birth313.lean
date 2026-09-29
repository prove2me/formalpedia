-- Prove2me | Theorems.Thm_Freiman_lower_guard_case_birth313
-- name    : Freiman.lower_guard_case_birth313
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:03:45.490398+00:00
-- url     : https://prove2.me/theorems/addaaf19-372d-4c47-8b32-abc92cc4c89d
-- title:
--   Freiman word guards: case birth313
-- statement:
--   Transfer the nine finite new-313 checks to actual suffixes. The effective guarded source excludes unguarded 33 and J1 alternatives.
-- source:
--   Freiman report, 'The complete boundary table for selected words', Appendix app:selection-words, report/source/staging/parts/word_certificates.tex; global_selection.tex admissibility argument; certificates/word_selection/selection_words_printed.json, word_guards.json and source_bindings.json; verification/families/word_selection/verify_word_guards.py.

import Definitions.Def_Freiman_lowerWordGuardData

open Freiman

theorem Freiman.lower_guard_case_birth313 (p : LowerPair) (c : LowerGuardCase) (hv : lowerGuardCaseValid c) (hf : lowerGuardFits c p)
    (l : LowerLabel) (hl : l ∈ c.labels) (right : Bool)
    (hnew : lowerEnds (lowerSide (lowerChild p l) right) [3,1,3])
    (hchanged : lowerSide (lowerChild p l) right ≠ lowerSide (lowerNormalize p) right) : l = ([2],[3]) := by
  sorry
