-- Prove2me | Theorems.Thm_NoHair_hansen_potential_of_lapse_radius
-- name    : NoHair.hansen_potential_of_lapse_radius
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-23T12:28:55.91937+00:00
-- url     : https://prove2.me/theorems/66bbdeba-1f6c-4e60-ad94-775a3782d164
-- title:
--   Smooth squared Hansen potential in the lapse-radius chart
-- statement:
--   In coordinates whose radius equals (1−N)/(1+N), the squared Hansen potential (N⁻¹−N)²/4 is exactly 4|y|²/(1−|y|²)². It has an explicit smooth extension with zero value at the added point.
-- source:
--   R. Beig and W. Simon, Proof of a multipole conjecture due to Geroch, Comm. Math. Phys. 78 (1980), 75–82, https://doi.org/10.1007/BF01941970. G. L. Bunting and A. K. M. Masood-ul-Alam, Nonexistence of multiple black holes in asymptotically Euclidean static vacuum space-time, Gen. Relativ. Gravit. 19 (1987), 147–154, https://doi.org/10.1007/BF00770326. These statements concern the lapse and its radial coordinate near the compactified end.

import Definitions.Def_NoHair_staticInvertedEndMetric

open NoHair Set Filter Metric
open scoped Topology ContDiff

theorem NoHair.hansen_potential_of_lapse_radius (δ : ℝ) (hδ : 0 < δ) (N : ADMPoint → ℝ) (e : ADMPoint → ADMPoint)
    (he : ∀ y ∈ ball (0:ADMPoint) δ, y ≠ 0 → 0 < N (e y) ∧ (1-N (e y))/(1+N (e y)) = ‖y‖) :
    ∃ f : ADMPoint → ℝ, f 0 = 0 ∧ ContDiffOn ℝ ∞ f (ball 0 (min δ 1)) ∧
      (∀ y ∈ ball (0:ADMPoint) (min δ 1), y ≠ 0 → f y = ((N (e y))⁻¹-N (e y))^2/4) ∧
      ∀ y ∈ ball (0:ADMPoint) (min δ 1), f y = 4*‖y‖^2/(1-‖y‖^2)^2 := by
  sorry
