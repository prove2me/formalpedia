-- Prove2me | Theorems.Thm_NoHair_static_lapse_euclidean_laplacian_and_flux_error
-- name    : NoHair.static_lapse_euclidean_laplacian_and_flux_error
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-23T11:39:22.851793+00:00
-- url     : https://prove2.me/theorems/2c8031a5-a4a3-4dc8-a9c9-7a513f02c1f3
-- title:
--   Euclidean Laplacian and flux errors for a static lapse at infinity
-- statement:
--   The Euclidean Laplacian of a static harmonic lapse decays as $r^{-4}$, and the volume-weighted raised gradient differs from its Euclidean gradient by $O(r^{-3})$. The assumed falloff bounds the first and second derivatives of the lapse and gives $h^{-1}-I=O(r^{-1})$. Contract the covariant Hessian equation to obtain the extra order of decay in the Euclidean trace.
-- source:
--   P. T. Chruściel, The classification of static vacuum space-times containing an asymptotically flat spacelike hypersurface with compact interior, Class. Quantum Grav. 16 (1999) 661–687, Proposition 3.3 and the static equations (5.4)–(5.6), https://homepage.univie.ac.at/piotr.chrusciel/papers/chrusciel/static.pdf. Bunting and Masood-ul-Alam, Gen. Relativ. Gravit. 19 (1987) 147–154, https://doi.org/10.1007/BF00770326.

import Definitions.Def_NoHair_staticHorizonGeometry
import Mathlib.Analysis.InnerProductSpace.Laplacian

open NoHair Set Filter Metric MeasureTheory InnerProductSpace
open scoped Topology ContDiff Laplacian

theorem NoHair.static_lapse_euclidean_laplacian_and_flux_error (Ω W : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (c : RegularRiemannianStaticEnd Ω W N h) :
    ∃ R C : ℝ, 0<R ∧ 0<C ∧ ∀ x : ADMPoint, R<‖x‖ →
      |(Δ N) x| ≤ C/‖x‖^4 ∧ ∀ i : Fin 3,
        |Real.sqrt (h x).det * staticRaisedGradient N h i x - spatialADMPartial i N x|
          ≤ C/‖x‖^3 := by sorry
