-- Prove2me | Theorems.Thm_KernelRank_eq_zero_of_sum_expPoly_eq_zero
-- name    : KernelRank.eq_zero_of_sum_expPoly_eq_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T02:01:04.005122+00:00
-- url     : https://prove2.me/theorems/67658ae6-2d50-46e6-a05f-7c50df3b165d
-- title:
--   Kernel Rank: eq zero of sum exp Poly eq zero
-- statement:
--   **Exponential polynomials vanish only trivially**: if `∑ μ ∈ S, P μ (u) · exp (μ u) = 0` for
--   all `u > 0`, then `P μ = 0` for every `μ ∈ S`.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/ExpPoly.lean#L111-L136
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/ExpPoly.lean#L111-L136

import Mathlib
import Definitions.Def_KernelRankLean_ExpPoly
set_option autoImplicit true
open Complex Polynomial
open KernelRank

theorem KernelRank.eq_zero_of_sum_expPoly_eq_zero (S : Finset ℂ) (P : ℂ → ℂ[X])
    (h : ∀ u : ℝ, 0 < u → ∑ μ ∈ S, expPoly (P μ) μ u = 0) : ∀ μ ∈ S, P μ = 0 := by sorry
