-- Prove2me | Theorems.Thm_NoHair_static_conformal_halves_scalar_flat
-- name    : NoHair.static_conformal_halves_scalar_flat
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-23T09:55:58.086843+00:00
-- url     : https://prove2.me/theorems/013adbba-9736-4c9b-8297-b5c9f57dd242
-- title:
--   Scalar flatness on both conformal halves of the static double
-- statement:
--   The original static metric has zero scalar curvature all the way to the regular horizon. Every nondegenerate rescaling $((1+sN)/2)^4h$ is also scalar flat, in particular the two choices $s=1,-1$ used in the conformal double. Both factors equal $1/2$ at the horizon.
-- source:
--   P. T. Chruściel, The classification of static vacuum space-times containing an asymptotically flat spacelike hypersurface with compact interior, Class. Quantum Grav. 16 (1999) 661–687, Proposition 3.3 and the static equations (5.4)–(5.6), https://homepage.univie.ac.at/piotr.chrusciel/papers/chrusciel/static.pdf. Bunting and Masood-ul-Alam, Gen. Relativ. Gravit. 19 (1987) 147–154, https://doi.org/10.1007/BF00770326.

import Definitions.Def_NoHair_staticHorizonGeometry

open NoHair Set Filter
open scoped ContDiff Manifold Topology

theorem NoHair.static_conformal_halves_scalar_flat (Ω W : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (c : RegularRiemannianStaticEnd Ω W N h) :
    ∀ x ∈ closure Ω, spatialScalarCurvature h x = 0 ∧
      ∀ s : ℝ, 1 + s * N x ≠ 0 →
        spatialScalarCurvature (staticPositiveMetric (fun y => s*N y) h) x = 0 := by sorry
