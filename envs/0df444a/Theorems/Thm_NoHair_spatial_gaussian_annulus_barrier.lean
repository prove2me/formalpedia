-- Prove2me | Theorems.Thm_NoHair_spatial_gaussian_annulus_barrier
-- name    : NoHair.spatial_gaussian_annulus_barrier
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T10:17:22.413015+00:00
-- url     : https://prove2.me/theorems/c57eaefc-53a1-4fb3-a237-2215155a1142
-- title:
--   Strictly subharmonic Gaussian barrier on a spatial annulus
-- statement:
--   On $r/2\le |x-y|\le r$ contained in the smooth positive-definite metric region, a sufficiently large $\alpha$ makes $\exp(-\alpha|x-y|^2)-\exp(-\alpha r^2)$ strictly subharmonic. Its derivative is nonzero on the outer sphere. The constants may depend on this compact annulus.
-- source:
--   D. Gilbarg and N. S. Trudinger, Elliptic Partial Differential Equations of Second Order, chapter 3, the spherical exponential barrier and the strong maximum principle, https://doi.org/10.1007/978-3-642-61798-0. P. T. Chruściel, The classification of static vacuum space-times containing an asymptotically flat spacelike hypersurface with compact interior, Class. Quantum Grav. 16 (1999) 661–687, Proposition 3.3 and the static equations (5.4)–(5.6), https://homepage.univie.ac.at/piotr.chrusciel/papers/chrusciel/static.pdf. Bunting and Masood-ul-Alam, Gen. Relativ. Gravit. 19 (1987) 147–154, https://doi.org/10.1007/BF00770326.

import Definitions.Def_NoHair_staticHorizonGeometry

open NoHair Set Filter
open scoped ContDiff Manifold Topology

theorem NoHair.spatial_gaussian_annulus_barrier (W : Set ADMPoint) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (hw : IsOpen W) (hh : ∀ i j, ContDiffOn ℝ ∞ (fun y => h y i j) W) (hp : ∀ x ∈ W, (h x).PosDef)
    (y : ADMPoint) (r : ℝ) (hr : 0<r) (ball : Metric.closedBall y r ⊆ W) :
    ∃ α : ℝ, 0 < α ∧
      let b := fun t : ADMPoint => Real.exp (-α * ‖t-y‖^2) - Real.exp (-α*r^2)
      ContDiff ℝ ∞ b ∧ (∀ x : ADMPoint, r/2 ≤ dist x y → dist x y ≤ r →
        0 < (∑ i : Fin 3, ∑ j : Fin 3, (h x)⁻¹ i j * staticSpatialHessian b h i j x)) ∧
      ∀ x : ADMPoint, dist x y = r → fderiv ℝ b x ≠ 0 := by sorry
