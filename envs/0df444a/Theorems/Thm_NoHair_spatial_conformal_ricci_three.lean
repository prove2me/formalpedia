-- Prove2me | Theorems.Thm_NoHair_spatial_conformal_ricci_three
-- name    : NoHair.spatial_conformal_ricci_three
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T09:57:39.238279+00:00
-- url     : https://prove2.me/theorems/cad8e65c-fc46-4397-ab1b-ec3d74149895
-- title:
--   Three-dimensional conformal Ricci tensor in arbitrary coordinates
-- statement:
--   The full Ricci tensor of $u^4 h$ is $\mathrm{Ric}(h)-2u^{-1}(D^2_h u+h\Delta_hu)+6u^{-2}du\otimes du-2u^{-2}|\nabla u|_h^2h$. The identity uses the coordinate tensors themselves and requires no field equation.
-- source:
--   P. T. Chruściel, The classification of static vacuum space-times containing an asymptotically flat spacelike hypersurface with compact interior, Class. Quantum Grav. 16 (1999) 661–687, Proposition 3.3 and the static equations (5.4)–(5.6), https://homepage.univie.ac.at/piotr.chrusciel/papers/chrusciel/static.pdf. Bunting and Masood-ul-Alam, Gen. Relativ. Gravit. 19 (1987) 147–154, https://doi.org/10.1007/BF00770326.

import Definitions.Def_NoHair_staticHorizonGeometry

open NoHair Set Filter
open scoped ContDiff Manifold Topology

theorem NoHair.spatial_conformal_ricci_three (u : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (W : Set ADMPoint) (hw : IsOpen W) (hu : ContDiffOn ℝ ∞ u W)
    (hh : ∀ i j, ContDiffOn ℝ ∞ (fun y => h y i j) W) (hp : ∀ x ∈ W, (h x).PosDef)
    (x : ADMPoint) (hx : x ∈ W) (hn : u x ≠ 0) :
    ∀ i j : Fin 3, spatialRicciTensor (fun y => (u y ^ 4) • h y) x i j =
      spatialRicciTensor h x i j - (2 / u x) * staticSpatialHessian u h i j x -
      (2 / u x) * h x i j *
        (∑ a : Fin 3, ∑ b : Fin 3, (h x)⁻¹ a b * staticSpatialHessian u h a b x) +
      (6 / u x ^ 2) * spatialADMPartial i u x * spatialADMPartial j u x -
      (2 / u x ^ 2) * h x i j * staticLapseGradientSq u h x := by sorry
