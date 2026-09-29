-- Prove2me | Theorems.Thm_Freiman_lower_guard_source_equal
-- name    : Freiman.lower_guard_source_equal
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:03:42.725446+00:00
-- url     : https://prove2.me/theorems/f0a713b7-2a18-4654-9704-d1e2293a6eff
-- title:
--   Freiman word guards: source equal
-- statement:
--   Match the actual guarded equal list to its explicit source row. Early and late routes contribute only their displayed candidate subsets; no numerical selection is inferred.
-- source:
--   Freiman report, 'The complete boundary table for selected words', Appendix app:selection-words, report/source/staging/parts/word_certificates.tex; global_selection.tex admissibility argument; certificates/word_selection/selection_words_printed.json, word_guards.json and source_bindings.json; verification/families/word_selection/verify_word_guards.py.

import Definitions.Def_Freiman_lowerWordGuardData

open Freiman

theorem Freiman.lower_guard_source_equal (p : LowerPair) (hp : lowerAdmissible p) (hpar : ¬ lowerMixed p)
    (l : LowerLabel) (hl : l ∈ lowerEqualList p) :
    ∃ c ∈ lowerGuardCases, lowerGuardFits c p ∧ l ∈ c.labels := by
  sorry
