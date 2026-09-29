-- Prove2me | Theorems.Thm_Freiman_lower_guard_source_run
-- name    : Freiman.lower_guard_source_run
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:03:30.492881+00:00
-- url     : https://prove2.me/theorems/dd49c201-2343-4d69-85b4-7483547d43c6
-- title:
--   Freiman word guards: source run
-- statement:
--   Bind the two finite repeated-3 representatives k=1,2 to the actual NN guard. Longer runs are handled by the separate boundary argument.
-- source:
--   Freiman report, 'The complete boundary table for selected words', Appendix app:selection-words, report/source/staging/parts/word_certificates.tex; global_selection.tex admissibility argument; certificates/word_selection/selection_words_printed.json, word_guards.json and source_bindings.json; verification/families/word_selection/verify_word_guards.py.

import Definitions.Def_Freiman_lowerWordGuardData

open Freiman

theorem Freiman.lower_guard_source_run (p : LowerPair) (hp : lowerAdmissible p) (hr : lowerRunOffered p) (k : ℕ) (hk : 0 < k) (hs : k < 3) :
    ∃ c ∈ lowerGuardCases, lowerGuardFits c p ∧ (List.replicate k 3,List.replicate k 3) ∈ c.labels := by
  sorry
