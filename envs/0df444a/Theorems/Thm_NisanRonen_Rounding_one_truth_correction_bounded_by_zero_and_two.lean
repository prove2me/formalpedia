-- Prove2me | Theorems.Thm_NisanRonen_Rounding_one_truth_correction_bounded_by_zero_and_two
-- name    : NisanRonen.Rounding.one_truth_correction_bounded_by_zero_and_two
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T07:50:14.795801+00:00
-- url     : https://prove2.me/theorems/45ca9ac1-1ccb-4295-8a1f-5636a4ab7b76
-- title:
--   The optimum after one truth correction is bounded by the endpoints of two corrections
-- statement:
--   Suppose two distinct machines use declaration-optimal reports with a bounded exact rounded solver. The rounded makespan of the reported allocation after the first row is corrected to truth is at most one grid step above the larger of its reported rounded makespan and the rounded makespan of any comparator after both rows are corrected. No tie-breaking hypothesis is required.
-- source:
--   Intermediate estimate for the report-certificate reduction of Nisan and Ronen (2001), Algorithmic Mechanism Design, Theorem 5.9.

import Definitions.Def_NisanRonen_Rounding_CertificateCriterion

namespace NisanRonen.Rounding

theorem one_truth_correction_bounded_by_zero_and_two {n k : ℕ} [NeZero n] {a b δ : ℝ} (hδ : 0 < δ)
    (f : List (Fin n → ℕ) → List (Fin n)) (hf : IsExactRoundedSolver f δ a b)
    (t d : Fin n → Fin k → ℝ)
    (ht : ∀ l j, a ≤ t l j ∧ t l j ≤ b) (hd : ∀ l j, a ≤ d l j ∧ d l j ≤ b)
    (i j : Fin n) (hij : i ≠ j)
    (hi : DeclarationOptimal f δ a b i (t i) (d i))
    (hj : DeclarationOptimal f δ a b j (t j) (d j)) (y : Fin k → Fin n) :
    let x := allocOf f δ d
    let di := Function.update d i (t i)
    let dij := Function.update di j (t j)
    roundedMakespan δ x (corrStar x di) ≤
      max (roundedMakespan δ x (corrStar x d))
        (roundedMakespan δ y (corrStar y dij)) + δ := by sorry

end NisanRonen.Rounding
