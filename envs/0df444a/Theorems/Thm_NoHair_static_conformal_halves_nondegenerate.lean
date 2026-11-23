-- Prove2me | Theorems.Thm_NoHair_static_conformal_halves_nondegenerate
-- name    : NoHair.static_conformal_halves_nondegenerate
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-23T10:17:27.656473+00:00
-- url     : https://prove2.me/theorems/7812031b-87f9-49c3-b793-672af7b509cf
-- title:
--   Both static conformal halves are nondegenerate and scalar flat up to the horizon
-- statement:
--   The static lapse is strictly less than one at each finite point of the closed exterior slice. It is positive in the interior and zero on the horizon. Both rescaled metrics $((1\pm N)/2)^4h$ are therefore positive definite and scalar flat at every such point.
-- source:
--   D. Gilbarg and N. S. Trudinger, Elliptic Partial Differential Equations of Second Order, chapter 3, the spherical exponential barrier and the strong maximum principle, https://doi.org/10.1007/978-3-642-61798-0. P. T. Chruściel, The classification of static vacuum space-times containing an asymptotically flat spacelike hypersurface with compact interior, Class. Quantum Grav. 16 (1999) 661–687, Proposition 3.3 and the static equations (5.4)–(5.6), https://homepage.univie.ac.at/piotr.chrusciel/papers/chrusciel/static.pdf. Bunting and Masood-ul-Alam, Gen. Relativ. Gravit. 19 (1987) 147–154, https://doi.org/10.1007/BF00770326.

import Definitions.Def_NoHair_staticHorizonGeometry

open NoHair Set Filter
open scoped ContDiff Manifold Topology

theorem NoHair.static_conformal_halves_nondegenerate (Ω W : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (c : RegularRiemannianStaticEnd Ω W N h) :
    ∀ x ∈ closure Ω, 0 ≤ N x ∧ N x < 1 ∧ ∀ s : ℝ, s=1 ∨ s=-1 →
      let k : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ := staticPositiveMetric (fun y => s*N y) h
      (k x).PosDef ∧ spatialScalarCurvature k x = 0 := by sorry
