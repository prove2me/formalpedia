-- Prove2me | Theorems.Thm_NoHair_spatial_harmonic_strong_maximum_three
-- name    : NoHair.spatial_harmonic_strong_maximum_three
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-23T10:17:29.044544+00:00
-- url     : https://prove2.me/theorems/695dc13b-42d2-4b1c-8e7d-5773dc1445de
-- title:
--   Strong maximum principle for a harmonic function of the spatial metric
-- statement:
--   On a connected open region with an arbitrary smooth positive-definite spatial metric, a smooth harmonic function attaining its maximum is constant. The proof uses a strictly subharmonic exponential barrier on a ball tangent to the set of maximum points.
-- source:
--   D. Gilbarg and N. S. Trudinger, Elliptic Partial Differential Equations of Second Order, chapter 3, the spherical exponential barrier and the strong maximum principle, https://doi.org/10.1007/978-3-642-61798-0. P. T. Chruściel, The classification of static vacuum space-times containing an asymptotically flat spacelike hypersurface with compact interior, Class. Quantum Grav. 16 (1999) 661–687, Proposition 3.3 and the static equations (5.4)–(5.6), https://homepage.univie.ac.at/piotr.chrusciel/papers/chrusciel/static.pdf. Bunting and Masood-ul-Alam, Gen. Relativ. Gravit. 19 (1987) 147–154, https://doi.org/10.1007/BF00770326.

import Definitions.Def_NoHair_staticHorizonGeometry

open NoHair Set Filter
open scoped ContDiff Manifold Topology

theorem NoHair.spatial_harmonic_strong_maximum_three (W : Set ADMPoint) (f : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (hw : IsOpen W) (hf : ContDiffOn ℝ ∞ f W) (hh : ∀ i j, ContDiffOn ℝ ∞ (fun y => h y i j) W) (hp : ∀ x ∈ W, (h x).PosDef)
    (hc : IsConnected W) (eq : ∀ y ∈ W, (∑ i : Fin 3, ∑ j : Fin 3, (h y)⁻¹ i j * staticSpatialHessian f h i j y) = 0)
    (x : ADMPoint) (hx : x∈W) (mx : ∀ y ∈ W, f y ≤ f x) : ∀ y ∈ W, f y = f x := by sorry
