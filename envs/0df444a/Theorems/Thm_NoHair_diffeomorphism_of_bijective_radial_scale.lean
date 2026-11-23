-- Prove2me | Theorems.Thm_NoHair_diffeomorphism_of_bijective_radial_scale
-- name    : NoHair.diffeomorphism_of_bijective_radial_scale
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T12:23:10.503905+00:00
-- url     : https://prove2.me/theorems/33cfca7f-cc70-4783-bdde-5c0945bc0d55
-- title:
--   A smooth inverse for a bijective radial coordinate map
-- statement:
--   A bijective radial scaling on two open sets is a diffeomorphism when its scalar factor and its radial differential are nowhere zero. This permits angular dependence of the factor.
-- source:
--   R. Beig and W. Simon, Proof of a multipole conjecture due to Geroch, Comm. Math. Phys. 78 (1980), 75–82, https://doi.org/10.1007/BF01941970. G. L. Bunting and A. K. M. Masood-ul-Alam, Nonexistence of multiple black holes in asymptotically Euclidean static vacuum space-time, Gen. Relativ. Gravit. 19 (1987), 147–154, https://doi.org/10.1007/BF00770326. These statements concern the lapse and its radial coordinate near the compactified end.

import Definitions.Def_NoHair_staticInvertedEndMetric

open NoHair Set Filter Metric
open scoped Topology ContDiff

theorem NoHair.diffeomorphism_of_bijective_radial_scale (u : ADMPoint → ℝ) (S T : Set ADMPoint) (hS : IsOpen S) (hT : IsOpen T)
    (bij : BijOn (fun x : ADMPoint => u x • x) S T)
    (reg : ∀ x ∈ S, ContDiffAt ℝ ∞ u x ∧ u x ≠ 0 ∧ u x + fderiv ℝ u x x ≠ 0) :
    ∃ e : OpenPartialHomeomorph ADMPoint ADMPoint, e.source = S ∧ e.target = T ∧
      (∀ x ∈ S, e x = u x • x) ∧ ContDiffOn ℝ ∞ e S ∧ ContDiffOn ℝ ∞ e.symm T := by
  sorry
