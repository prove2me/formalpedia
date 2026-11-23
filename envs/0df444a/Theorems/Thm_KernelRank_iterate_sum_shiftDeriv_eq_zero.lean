-- Prove2me | Theorems.Thm_KernelRank_iterate_sum_shiftDeriv_eq_zero
-- name    : KernelRank.iterate_sum_shiftDeriv_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:58:30.413534+00:00
-- url     : https://prove2.me/theorems/f67c6d08-aa85-465f-9d5c-0c9f77a0af4f
-- title:
--   Kernel Rank: iterate sum shift Deriv eq zero
-- statement:
--   The Kernel Rank construction uses the iterate sum shift Deriv eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/ExpPoly.lean#L72-L79
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/ExpPoly.lean#L72-L79

import Mathlib
import Definitions.Def_KernelRankLean_ExpPoly
set_option autoImplicit true
open Complex Polynomial
open KernelRank

theorem KernelRank.iterate_sum_shiftDeriv_eq_zero {S : Finset ℂ} {P : ℂ → ℂ[X]} (a : ℂ) (n : ℕ)
    (h : ∀ u : ℝ, 0 < u → ∑ μ ∈ S, expPoly (P μ) μ u = 0) :
    ∀ u : ℝ, 0 < u → ∑ μ ∈ S, expPoly ((shiftDeriv a μ)^[n] (P μ)) μ u = 0 := by sorry
