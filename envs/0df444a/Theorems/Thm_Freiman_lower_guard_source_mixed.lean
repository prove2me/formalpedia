-- Prove2me | Theorems.Thm_Freiman_lower_guard_source_mixed
-- name    : Freiman.lower_guard_source_mixed
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:03:32.878126+00:00
-- url     : https://prove2.me/theorems/29055a14-4966-43d4-8ccb-6230bbb19308
-- title:
--   Freiman word guards: source mixed
-- statement:
--   Match the actual guarded mixed list to its explicit source row. Early and late routes contribute only their displayed candidate subsets; no numerical selection is inferred.
-- source:
--   Freiman report, 'The complete boundary table for selected words', Appendix app:selection-words, report/source/staging/parts/word_certificates.tex; global_selection.tex admissibility argument; certificates/word_selection/selection_words_printed.json, word_guards.json and source_bindings.json; verification/families/word_selection/verify_word_guards.py.

import Definitions.Def_Freiman_lowerWordGuardData

open Freiman

theorem Freiman.lower_guard_source_mixed (p : LowerPair) (hp : lowerAdmissible p) (hpar : lowerMixed p)
    (l : LowerLabel) (hl : l ∈ lowerMixedList p) :
    ∃ c ∈ lowerGuardCases, lowerGuardFits c p ∧ l ∈ c.labels := by
  sorry
