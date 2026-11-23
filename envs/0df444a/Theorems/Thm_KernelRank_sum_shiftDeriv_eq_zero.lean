-- Prove2me | Theorems.Thm_KernelRank_sum_shiftDeriv_eq_zero
-- name    : KernelRank.sum_shiftDeriv_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:58:29.985802+00:00
-- url     : https://prove2.me/theorems/954354b4-22f8-4f31-bef8-079744bb05b5
-- title:
--   Kernel Rank: sum shift Deriv eq zero
-- statement:
--   `d/du - a` preserves vanishing on `u > 0`.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/ExpPoly.lean#L49-L70
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/ExpPoly.lean#L49-L70

import Mathlib
import Definitions.Def_KernelRankLean_ExpPoly
set_option autoImplicit true
open Complex Polynomial
open KernelRank

theorem KernelRank.sum_shiftDeriv_eq_zero {S : Finset ℂ} {P : ℂ → ℂ[X]} (a : ℂ)
    (h : ∀ u : ℝ, 0 < u → ∑ μ ∈ S, expPoly (P μ) μ u = 0) :
    ∀ u : ℝ, 0 < u → ∑ μ ∈ S, expPoly (shiftDeriv a μ (P μ)) μ u = 0 := by sorry
