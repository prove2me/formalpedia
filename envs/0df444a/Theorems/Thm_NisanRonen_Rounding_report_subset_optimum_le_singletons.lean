-- Prove2me | Theorems.Thm_NisanRonen_Rounding_report_subset_optimum_le_singletons
-- name    : NisanRonen.Rounding.report_subset_optimum_le_singletons
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T08:00:50.242515+00:00
-- url     : https://prove2.me/theorems/5950fd08-93a1-45c1-9c9c-4cb2241e12a3
-- title:
--   Single-report optima bound every mixture of declared and true rows
-- statement:
--   Suppose each declared row is declaration-optimal, the true profile has an allocation of rounded cost at most C, and each profile with just one declared row and all other rows true has rounded optimum at most C. Then every mixture of the declared and true rows has rounded optimum at most C.
-- source:
--   Report-certificate reduction for Nisan and Ronen (2001), Algorithmic Mechanism Design, Theorem 5.9.

import Definitions.Def_NisanRonen_Rounding_CertificateCriterion

namespace NisanRonen.Rounding

theorem report_subset_optimum_le_singletons {n k : ℕ} [NeZero n] {a b δ C : ℝ}
    (f : List (Fin n → ℕ) → List (Fin n)) (hf : IsExactRoundedSolver f δ a b)
    (t d : Fin n → Fin k → ℝ) (ht : ∀ l j, a ≤ t l j ∧ t l j ≤ b)
    (hd : ∀ l j, a ≤ d l j ∧ d l j ≤ b)
    (hop : ∀ i, DeclarationOptimal f δ a b i (t i) (d i))
    (y : Fin k → Fin n) (hy : roundedMakespan δ y (corrStar y t) ≤ C)
    (hsingle : ∀ i, let v := Function.update t i (d i)
      roundedMakespan δ (allocOf f δ v) (corrStar (allocOf f δ v) v) ≤ C)
    (S : Finset (Fin n)) :
    let v (l : Fin n) := if l ∈ S then d l else t l
    roundedMakespan δ (allocOf f δ v) (corrStar (allocOf f δ v) v) ≤ C := by sorry

end NisanRonen.Rounding
