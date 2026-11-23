-- Prove2me | Theorems.Thm_NoHair_spatial_laplacian_in_divergence_form
-- name    : NoHair.spatial_laplacian_in_divergence_form
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T10:30:56.695426+00:00
-- url     : https://prove2.me/theorems/5f3aa867-5d9d-4fa8-ade3-e3f39e386457
-- title:
--   Divergence form of the spatial Laplace–Beltrami operator
-- statement:
--   In a smooth positive-definite chart, the coordinate divergence of the volume-weighted raised gradient is $\sqrt{\det h}\,\Delta_h f$. This identifies the harmonic static lapse equation with the physical flux conservation law.
-- source:
--   P. T. Chruściel, The classification of static vacuum space-times containing an asymptotically flat spacelike hypersurface with compact interior, Class. Quantum Grav. 16 (1999) 661–687, Proposition 3.3 and the static equations (5.4)–(5.6), https://homepage.univie.ac.at/piotr.chrusciel/papers/chrusciel/static.pdf. Bunting and Masood-ul-Alam, Gen. Relativ. Gravit. 19 (1987) 147–154, https://doi.org/10.1007/BF00770326.

import Definitions.Def_NoHair_staticHorizonGeometry

open NoHair Set Filter
open scoped ContDiff Manifold Topology

theorem NoHair.spatial_laplacian_in_divergence_form (f : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (W : Set ADMPoint) (hw : IsOpen W) (hf : ContDiffOn ℝ ∞ f W)
    (hh : ∀ i j, ContDiffOn ℝ ∞ (fun y => h y i j) W) (hp : ∀ x ∈ W, (h x).PosDef) (x : ADMPoint) (hx : x∈W) :
    (∑ i : Fin 3, spatialADMPartial i (fun y => Real.sqrt (h y).det * staticRaisedGradient f h i y) x) =
      Real.sqrt (h x).det * (∑ i : Fin 3, ∑ j : Fin 3, (h x)⁻¹ i j * staticSpatialHessian f h i j x) := by sorry
