-- Prove2me | Theorems.Thm_Freiman_lower_priority_finite_selection
-- name    : Freiman.lower_priority_finite_selection
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:17:37.02983+00:00
-- url     : https://prove2.me/theorems/9ab7739a-a7d4-4e85-9779-1ad9dcc3fbae
-- title:
--   Freiman lower construction: priority finite selection
-- statement:
--   Elementary finite-priority selection: replace a blocked candidate by an eligible preferred candidate. The two source branches are disjoint and preferred candidates cannot themselves be blocked on the same branch.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/global_selection.tex, compatible priority selection

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_priority_finite_selection (t : ℝ) (p : LowerPair) (hp : lowerPreferredGood p)
    (h : ∃ l : LowerLabel, lowerOffered p l ∧ lowerGood (lowerChild p l) ∧ t ∈ lowerCover (lowerChild p l)) :
    ∃ l : LowerLabel, lowerOffered p l ∧ lowerPriority t p l ∧ lowerGood (lowerChild p l) ∧ t ∈ lowerCover (lowerChild p l) := by
  sorry
