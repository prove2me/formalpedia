-- Prove2me | Theorems.Thm_NoHair_static_block_ricci_hessian_identities
-- name    : NoHair.static_block_ricci_hessian_identities
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-23T09:16:43.906804+00:00
-- url     : https://prove2.me/theorems/f8d01350-2ddd-448d-b426-62a21d8e1dd7
-- title:
--   Exact Ricci tensor of a static spacetime
-- statement:
--   For any smooth static metric $g=-N^2dt^2+h$ with $h$ positive definite and $N\ne0$, its time-time Ricci component is $N\Delta_hN$. Its spatial block is $\mathrm{Ric}_h-N^{-1}D_h^2N$. Both formulas hold before imposing any field equation.
-- source:
--   P. T. Chruściel, The classification of static vacuum space-times containing an asymptotically flat spacelike hypersurface with compact interior, Class. Quantum Grav. 16 (1999) 661–687, Proposition 3.3 and the static equations (5.4)–(5.6), https://homepage.univie.ac.at/piotr.chrusciel/papers/chrusciel/static.pdf. Bunting and Masood-ul-Alam, Gen. Relativ. Gravit. 19 (1987) 147–154, https://doi.org/10.1007/BF00770326.

import Definitions.Def_NoHair_staticHorizonGeometry

open NoHair Set Filter
open scoped ContDiff Manifold Topology

theorem NoHair.static_block_ricci_hessian_identities (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (W : Set ADMPoint) (hw : IsOpen W) (hn : ContDiffOn ℝ ∞ N W)
    (hh : ∀ i j, ContDiffOn ℝ ∞ (fun y => h y i j) W) (hp : ∀ x ∈ W, (h x).PosDef)
    (x : ADMPoint) (hx : x ∈ W) (nz : N x ≠ 0) :
    ricci (staticCartesianBlock N h) (staticTimeZero x) 0 0 =
      N x * ∑ i : Fin 3, ∑ j : Fin 3, (h x)⁻¹ i j * staticSpatialHessian N h i j x ∧
    ∀ i j : Fin 3, ricci (staticCartesianBlock N h) (staticTimeZero x) i.succ j.succ =
      spatialRicciTensor h x i j - staticSpatialHessian N h j i x / N x := by sorry
