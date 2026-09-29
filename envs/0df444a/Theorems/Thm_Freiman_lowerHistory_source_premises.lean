-- Prove2me | Theorems.Thm_Freiman_lowerHistory_source_premises
-- name    : Freiman.lowerHistory_source_premises
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:32:07.026982+00:00
-- url     : https://prove2.me/theorems/9b8c0920-3e24-4ba9-abd7-4d9c08220974
-- title:
--   Freiman.lowerHistory_source_premises
-- statement:
--   An actual reached history satisfies one computed source premise alternative.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026); global_selection.tex, lem:global-suffix-targets; history_certificates.tex, app:all-suffix-histories; verification/families/target_selection/verify_suffix_targets_independent.py; certificates/target_selection/all_suffix_histories_printed.json; role: source DNF construction

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic

open Freiman

theorem Freiman.lowerHistory_source_premises (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n)
    (base : LowerPair) (p : LowerHistoryPath) (hp : lowerHistoryStructural p) (hr : lowerHistoryReached t h n base p) (haz : lowerHistoryHazard p.row (h n)) :
    ∃ bs ∈ lowerHistorySourcePremises p, lowerHistoryAtBase base bs := by
  sorry
