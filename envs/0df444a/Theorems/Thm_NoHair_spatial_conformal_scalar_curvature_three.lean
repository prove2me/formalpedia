-- Prove2me | Theorems.Thm_NoHair_spatial_conformal_scalar_curvature_three
-- name    : NoHair.spatial_conformal_scalar_curvature_three
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-23T09:56:14.421798+00:00
-- url     : https://prove2.me/theorems/1fdfbd28-7947-4ee7-a418-86af27811975
-- title:
--   Three-dimensional conformal scalar curvature formula in an arbitrary chart
-- statement:
--   For a smooth positive-definite three-dimensional metric $h$ and any smooth nonvanishing conformal factor $u$, the actual scalar curvatures satisfy $u^5 R(u^4h)=uR(h)-8\Delta_h u$. This holds at every point where $u\ne0$, without any field equation or symmetry assumption.
-- source:
--   P. T. Chruściel, The classification of static vacuum space-times containing an asymptotically flat spacelike hypersurface with compact interior, Class. Quantum Grav. 16 (1999) 661–687, Proposition 3.3 and the static equations (5.4)–(5.6), https://homepage.univie.ac.at/piotr.chrusciel/papers/chrusciel/static.pdf. Bunting and Masood-ul-Alam, Gen. Relativ. Gravit. 19 (1987) 147–154, https://doi.org/10.1007/BF00770326.

import Definitions.Def_NoHair_staticHorizonGeometry

open NoHair Set Filter
open scoped ContDiff Manifold Topology

theorem NoHair.spatial_conformal_scalar_curvature_three (u : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (W : Set ADMPoint) (hw : IsOpen W) (hu : ContDiffOn ℝ ∞ u W)
    (hh : ∀ i j, ContDiffOn ℝ ∞ (fun y => h y i j) W) (hp : ∀ x ∈ W, (h x).PosDef)
    (x : ADMPoint) (hx : x ∈ W) (hn : u x ≠ 0) :
    u x ^ 5 * spatialScalarCurvature (fun y => (u y ^ 4) • h y) x =
      u x * spatialScalarCurvature h x -
        8 * (∑ i : Fin 3, ∑ j : Fin 3, (h x)⁻¹ i j * staticSpatialHessian u h i j x) := by sorry
