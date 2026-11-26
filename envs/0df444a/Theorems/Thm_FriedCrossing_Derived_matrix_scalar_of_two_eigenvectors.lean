-- Prove2me | Theorems.Thm_FriedCrossing_Derived_matrix_scalar_of_two_eigenvectors
-- name    : FriedCrossing.Derived.matrix_scalar_of_two_eigenvectors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:51:16.679321+00:00
-- url     : https://prove2.me/theorems/9d5a07c1-febd-5622-a67a-19603c508eac
-- title:
--   Derived: matrix scalar of two eigenvectors
-- statement:
--   SATURATION, matrix form. Two linearly independent eigenvectors of a real 2×2 matrix with the same
--   eigenvalue s force the matrix to be s·1: the rank (2, the type) plus two independent resonant states
--   at s*(θ) — d₀f and I·d₀f (rederivation A2) — give M(θ,0) = s*(θ)·1, the former binder `hsemisimple`.
--   Wraps `Saturation.scalar_of_two_eigenvectors` (rate file §6) through `Matrix.toLin'`.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L703-L716
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L703-L716

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Derived

theorem FriedCrossing.Derived.matrix_scalar_of_two_eigenvectors (M : Matrix (Fin 2) (Fin 2) ℝ) (s : ℝ)
    (v₁ v₂ : Fin 2 → ℝ) (hind : LinearIndependent ℝ ![v₁, v₂])
    (h₁ : M *ᵥ v₁ = s • v₁) (h₂ : M *ᵥ v₂ = s • v₂) :
    M = s • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by sorry
