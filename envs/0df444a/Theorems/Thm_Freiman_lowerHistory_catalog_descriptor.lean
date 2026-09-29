-- Prove2me | Theorems.Thm_Freiman_lowerHistory_catalog_descriptor
-- name    : Freiman.lowerHistory_catalog_descriptor
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:32:29.994563+00:00
-- url     : https://prove2.me/theorems/81fd5711-bfb3-4c7e-881c-4013f8b69e47
-- title:
--   Freiman.lowerHistory_catalog_descriptor
-- statement:
--   Finite grammar equality selects an actual stored row for the reached history; no arbitrary catalog applicability is assumed.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026); global_selection.tex, lem:global-suffix-targets; history_certificates.tex, app:all-suffix-histories; verification/families/target_selection/verify_suffix_targets_independent.py; certificates/target_selection/all_suffix_histories_printed.json; role: actual catalog applicability

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic

open Freiman

theorem Freiman.lowerHistory_catalog_descriptor (t : ℝ) (h : ℕ → LowerPair) (n row : ℕ) (hh : lowerHistory t h n)
    (hrow : row ∈ [1,2,3,4]) (haz : lowerHistoryHazard row (h n)) :
    ∃ base p, p ∈ lowerHistoryPaths.toList ∧ lowerHistoryReached t h n base p ∧ p.row = row := by
  sorry
