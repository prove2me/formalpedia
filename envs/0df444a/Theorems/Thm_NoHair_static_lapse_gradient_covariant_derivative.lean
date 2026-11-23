-- Prove2me | Theorems.Thm_NoHair_static_lapse_gradient_covariant_derivative
-- name    : NoHair.static_lapse_gradient_covariant_derivative
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T09:16:51.543461+00:00
-- url     : https://prove2.me/theorems/fcfe724d-42c2-442b-9b89-476905e0dbbc
-- title:
--   Covariant derivative of the raised lapse gradient and of its squared norm
-- statement:
--   Metric compatibility identifies the covariant derivative of the raised gradient with the raised covariant Hessian. It gives $\partial_i |\nabla N|_h^2=2(D_h^2N)_{ij}(\nabla N)^j$. All quantities use the same spatial coordinate metric.
-- source:
--   P. T. Chruściel, The classification of static vacuum space-times containing an asymptotically flat spacelike hypersurface with compact interior, Class. Quantum Grav. 16 (1999) 661–687, Proposition 3.3 and the static equations (5.4)–(5.6), https://homepage.univie.ac.at/piotr.chrusciel/papers/chrusciel/static.pdf. Bunting and Masood-ul-Alam, Gen. Relativ. Gravit. 19 (1987) 147–154, https://doi.org/10.1007/BF00770326.

import Definitions.Def_NoHair_staticHorizonGeometry

open NoHair Set Filter
open scoped ContDiff Manifold Topology

theorem NoHair.static_lapse_gradient_covariant_derivative (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (W : Set ADMPoint) (hw : IsOpen W) (hn : ContDiffOn ℝ ∞ N W)
    (hh : ∀ i j, ContDiffOn ℝ ∞ (fun y => h y i j) W) (hp : ∀ x ∈ W, (h x).PosDef)
    (x : ADMPoint) (hx : x ∈ W) (i : Fin 3) :
    (∀ a : Fin 3, spatialADMPartial i (staticRaisedGradient N h a) x +
      (∑ l : Fin 3, spatialLeviCivita h x a i l * staticRaisedGradient N h l x) =
      ∑ j : Fin 3, (h x)⁻¹ a j * staticSpatialHessian N h i j x) ∧
    spatialADMPartial i (staticLapseGradientSq N h) x =
      2 * ∑ j : Fin 3, staticSpatialHessian N h i j x * staticRaisedGradient N h j x := by sorry
