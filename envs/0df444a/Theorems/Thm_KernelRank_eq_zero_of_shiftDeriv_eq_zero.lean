-- Prove2me | Theorems.Thm_KernelRank_eq_zero_of_shiftDeriv_eq_zero
-- name    : KernelRank.eq_zero_of_shiftDeriv_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:59:58.316526+00:00
-- url     : https://prove2.me/theorems/e2d64a4f-6545-42fb-84cf-a456281e4856
-- title:
--   Kernel Rank: eq zero of shift Deriv eq zero
-- statement:
--   For `μ ≠ a`, `shiftDeriv a μ` is injective: it keeps the leading coefficient times `μ - a`.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/ExpPoly.lean#L85-L91
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/ExpPoly.lean#L85-L91

import Mathlib
import Definitions.Def_KernelRankLean_ExpPoly
set_option autoImplicit true
open Complex Polynomial
open KernelRank

theorem KernelRank.eq_zero_of_shiftDeriv_eq_zero {a μ : ℂ} (hμ : μ ≠ a) {P : ℂ[X]}
    (h : shiftDeriv a μ P = 0) : P = 0 := by sorry
