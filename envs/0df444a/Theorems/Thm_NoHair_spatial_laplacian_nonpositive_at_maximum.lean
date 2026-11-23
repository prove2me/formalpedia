-- Prove2me | Theorems.Thm_NoHair_spatial_laplacian_nonpositive_at_maximum
-- name    : NoHair.spatial_laplacian_nonpositive_at_maximum
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T10:17:18.673254+00:00
-- url     : https://prove2.me/theorems/f0470b6a-34b6-4478-980a-5ff8c69c9485
-- title:
--   Sign of the spatial Laplacian at an interior maximum
-- statement:
--   At an interior local maximum of a smooth real function, its covariant Laplacian for a positive-definite spatial metric is nonpositive. The first derivatives vanish. Factoring the inverse metric reduces the Hessian trace to a sum of second directional derivatives.
-- source:
--   D. Gilbarg and N. S. Trudinger, Elliptic Partial Differential Equations of Second Order, chapter 3, the spherical exponential barrier and the strong maximum principle, https://doi.org/10.1007/978-3-642-61798-0. P. T. Chruściel, The classification of static vacuum space-times containing an asymptotically flat spacelike hypersurface with compact interior, Class. Quantum Grav. 16 (1999) 661–687, Proposition 3.3 and the static equations (5.4)–(5.6), https://homepage.univie.ac.at/piotr.chrusciel/papers/chrusciel/static.pdf. Bunting and Masood-ul-Alam, Gen. Relativ. Gravit. 19 (1987) 147–154, https://doi.org/10.1007/BF00770326.

import Definitions.Def_NoHair_staticHorizonGeometry

open NoHair Set Filter
open scoped ContDiff Manifold Topology

theorem NoHair.spatial_laplacian_nonpositive_at_maximum (W : Set ADMPoint) (f : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (hw : IsOpen W) (hf : ContDiffOn ℝ ∞ f W) 
    (x : ADMPoint) (hx : x∈W) (hp : (h x).PosDef) (hm : IsLocalMax f x) :
    (∑ i : Fin 3, ∑ j : Fin 3, (h x)⁻¹ i j * staticSpatialHessian f h i j x) ≤ 0 := by sorry
