-- Prove2me | Theorems.Thm_NoHair_regular_static_lapse_level_spheres_at_infinity
-- name    : NoHair.regular_static_lapse_level_spheres_at_infinity
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T12:14:03.444055+00:00
-- url     : https://prove2.me/theorems/76438e3f-923f-46c9-8ae4-f4454d88de48
-- title:
--   Every large static lapse level meets each ray exactly once
-- statement:
--   Outside one coordinate sphere the static lapse has strictly positive radial derivative in all directions. Every level sufficiently close to one meets each outgoing ray at exactly one radius.
-- source:
--   R. Beig and W. Simon, Proof of a multipole conjecture due to Geroch, Comm. Math. Phys. 78 (1980), 75–82, https://doi.org/10.1007/BF01941970. G. L. Bunting and A. K. M. Masood-ul-Alam, Nonexistence of multiple black holes in asymptotically Euclidean static vacuum space-time, Gen. Relativ. Gravit. 19 (1987), 147–154, https://doi.org/10.1007/BF00770326. These statements concern the lapse and its radial coordinate near the compactified end.

import Definitions.Def_NoHair_staticInvertedEndMetric

open NoHair Set Filter Metric
open scoped Topology ContDiff

theorem NoHair.regular_static_lapse_level_spheres_at_infinity (Ω W : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (c : RegularRiemannianStaticEnd Ω W N h) :
    ∃ R L : ℝ, 0 < R ∧ 0 < L ∧ L < 1 ∧
      (∀ x : ADMPoint, R ≤ ‖x‖ → 0 < N x ∧ N x < 1 ∧ 0 < fderiv ℝ N x x) ∧
      (∀ n : ADMSphere, StrictMonoOn (fun r : ℝ => N (r • (n:ADMPoint))) (Ici R)) ∧
      ∀ n : ADMSphere, ∀ t : ℝ, L < t → t < 1 →
        ∃! r : ℝ, R < r ∧ N (r • (n:ADMPoint)) = t := by
  sorry
