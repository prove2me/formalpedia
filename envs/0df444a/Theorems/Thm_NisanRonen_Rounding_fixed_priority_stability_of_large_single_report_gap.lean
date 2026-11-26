-- Prove2me | Theorems.Thm_NisanRonen_Rounding_fixed_priority_stability_of_large_single_report_gap
-- name    : NisanRonen.Rounding.fixed_priority_stability_of_large_single_report_gap
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T08:00:34.865854+00:00
-- url     : https://prove2.me/theorems/835cca32-d39e-59ac-8d5c-814b7deb1132
-- title:
--   A large single-report gap fixes the chosen allocation throughout a truth-feasible region
-- statement:
--   Fix an exact bounded rounded solver with an injective report-independent priority. Suppose the focal declaration is declaration-optimal, a comparator is feasible at grid threshold C at the true profile, and the profile with just the focal declared row has rounded optimum above C + δ. Then for every bounded opponent profile at which focal truth correction allows cost at most C, the solver selects the same allocation and reported optimum as at the single-report profile. Its focal truth-corrected cost is at most C.
-- source:
--   Report-certificate reduction for Nisan and Ronen (2001), Algorithmic Mechanism Design, Theorem 5.9.

import Definitions.Def_NisanRonen_Rounding_CertificateCriterion

namespace NisanRonen.Rounding

theorem fixed_priority_stability_of_large_single_report_gap {n k : ℕ} [NeZero n] {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ)
    (f : List (Fin n → ℕ) → List (Fin n)) (hf : IsExactRoundedSolver f δ a b)
    (rank : (Fin k → Fin n) → ℕ) (hinj : Function.Injective rank)
    (hpriority : ∀ v : Fin n → Fin k → ℝ, (∀ l j, a ≤ v l j ∧ v l j ≤ b) →
      ∀ y : Fin k → Fin n, roundedMakespan δ y (corrStar y v) =
        roundedMakespan δ (allocOf f δ v) (corrStar (allocOf f δ v) v) →
        rank (allocOf f δ v) ≤ rank y)
    (t d : Fin n → Fin k → ℝ) (ht : ∀ l j, a ≤ t l j ∧ t l j ≤ b)
    (hd : ∀ l j, a ≤ d l j ∧ d l j ≤ b)
    (i : Fin n) (hop : DeclarationOptimal f δ a b i (t i) (d i)) (m : ℤ)
    (y : Fin k → Fin n) (hy : roundedMakespan δ y (corrStar y t) ≤ δ * (m : ℝ)) :
    let s := Function.update t i (d i)
    let x := allocOf f δ s
    δ * (m : ℝ) + δ < roundedMakespan δ x (corrStar x s) →
    ∀ v : Fin n → Fin k → ℝ, (∀ l j, a ≤ v l j ∧ v l j ≤ b) → v i = d i →
      (∃ z : Fin k → Fin n,
        roundedMakespan δ z (corrStar z (Function.update v i (t i))) ≤ δ * (m : ℝ)) →
      allocOf f δ v = x ∧
      roundedMakespan δ x (corrStar x (Function.update v i (t i))) ≤ δ * (m : ℝ) ∧
      roundedMakespan δ x (corrStar x v) = roundedMakespan δ x (corrStar x s) := by sorry

end NisanRonen.Rounding
