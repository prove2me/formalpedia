-- Prove2me | Theorems.Thm_Freiman_lowerHistory_generic_descriptor
-- name    : Freiman.lowerHistory_generic_descriptor
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:32:24.474262+00:00
-- url     : https://prove2.me/theorems/46934c1a-de1c-4b38-b6f8-9545630e5074
-- title:
--   Freiman.lowerHistory_generic_descriptor
-- statement:
--   Extract the actual 23 birth and preserved physical suffix; the six terminal contexts and source labels produce a legal descriptor of length at most seven.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026); global_selection.tex, lem:global-suffix-targets; history_certificates.tex, app:all-suffix-histories; verification/families/target_selection/verify_suffix_targets_independent.py; certificates/target_selection/all_suffix_histories_printed.json; role: source birth-to-hazard classification

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic

open Freiman

theorem Freiman.lowerHistory_generic_descriptor (hf : ∀ (p : LowerPair), lowerGood p → lowerParameterBox p → let q := lowerNormalize p; lowerWidth (q.1++[2]) < lowerWidth q.2 ∧ lowerWidth (q.1++[3]) < lowerWidth q.2 ∧ lowerWidth (q.1++[1,1]) < lowerWidth q.2 ∧ lowerWidth (q.2++[1]) < lowerWidth q.1) (t : ℝ) (h : ℕ → LowerPair) (n row : ℕ) (hh : lowerHistory t h n)
    (hrow : row ∈ [1,2,3,4]) (haz : lowerHistoryHazard row (h n))
    (hm : lowerGenericMarked h n (lowerMarkedPhysical h n row)) :
    ∃ base p, lowerHistoryStructural p ∧ lowerHistoryReached t h n base p ∧ p.row = row := by
  sorry
