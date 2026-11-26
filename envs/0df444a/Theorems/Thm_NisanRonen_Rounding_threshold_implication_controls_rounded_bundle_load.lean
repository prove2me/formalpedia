-- Prove2me | Theorems.Thm_NisanRonen_Rounding_threshold_implication_controls_rounded_bundle_load
-- name    : NisanRonen.Rounding.threshold_implication_controls_rounded_bundle_load
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T08:00:59.488725+00:00
-- url     : https://prove2.me/theorems/e39a6bd8-7dd3-4bc6-85ba-1bf386cd0617
-- title:
--   A universal threshold implication orders rounded bundle loads above the threshold
-- statement:
--   Suppose the minimum rounded load of S is at most the grid threshold C, and every bounded row that gives S load at most C also gives T load at most C. Then for any bounded row r whose load on T exceeds C, its load on T is at most its load on S.
-- source:
--   Report-certificate reduction for Nisan and Ronen (2001), Algorithmic Mechanism Design, Theorem 5.9.

import Definitions.Def_NisanRonen_Rounding_CertificateCriterion

namespace NisanRonen.Rounding

theorem threshold_implication_controls_rounded_bundle_load {k : ℕ} {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ)
    (S T : Finset (Fin k)) (m : ℤ)
    (hfloor : (∑ _j ∈ S, roundUp δ a) ≤ δ * (m : ℝ))
    (himp : ∀ p : Fin k → ℝ, (∀ j, a ≤ p j ∧ p j ≤ b) →
      (∑ j ∈ S, roundUp δ (p j)) ≤ δ * (m : ℝ) →
      (∑ j ∈ T, roundUp δ (p j)) ≤ δ * (m : ℝ))
    (r : Fin k → ℝ) (hr : ∀ j, a ≤ r j ∧ r j ≤ b)
    (hrT : δ * (m : ℝ) < ∑ j ∈ T, roundUp δ (r j)) :
    (∑ j ∈ T, roundUp δ (r j)) ≤ ∑ j ∈ S, roundUp δ (r j) := by sorry

end NisanRonen.Rounding
