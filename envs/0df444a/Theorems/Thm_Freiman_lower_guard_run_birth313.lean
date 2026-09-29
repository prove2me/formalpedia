-- Prove2me | Theorems.Thm_Freiman_lower_guard_run_birth313
-- name    : Freiman.lower_guard_run_birth313
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:03:54.863621+00:00
-- url     : https://prove2.me/theorems/c9b47686-2390-411d-bd52-d4e62fc6e9a0
-- title:
--   Freiman word guards: run birth313
-- statement:
--   A long repeated-3 continuation ends in 33 on both sides, so cannot create a final 313.
-- source:
--   Freiman report, 'The complete boundary table for selected words', Appendix app:selection-words, report/source/staging/parts/word_certificates.tex; global_selection.tex admissibility argument; certificates/word_selection/selection_words_printed.json, word_guards.json and source_bindings.json; verification/families/word_selection/verify_word_guards.py.

import Definitions.Def_Freiman_lowerWordGuardData

open Freiman

theorem Freiman.lower_guard_run_birth313 (p : LowerPair) (k : ℕ) (hk : 3 ≤ k) (right : Bool) :
    ¬ lowerEnds (lowerSide (lowerChild p (List.replicate k 3,List.replicate k 3)) right) [3,1,3] := by
  sorry
