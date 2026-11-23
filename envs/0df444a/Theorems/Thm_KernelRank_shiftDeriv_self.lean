-- Prove2me | Theorems.Thm_KernelRank_shiftDeriv_self
-- name    : KernelRank.shiftDeriv_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T02:00:00.320652+00:00
-- url     : https://prove2.me/theorems/fcc335f7-72ba-4a8f-b843-70a887e2592e
-- title:
--   Kernel Rank: shift Deriv self
-- statement:
--   The Kernel Rank construction uses the shift Deriv self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/ExpPoly.lean#L81-L82
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/ExpPoly.lean#L81-L82

import Mathlib
import Definitions.Def_KernelRankLean_ExpPoly
set_option autoImplicit true
open Complex Polynomial
open KernelRank

theorem KernelRank.shiftDeriv_self (a : ℂ) (P : ℂ[X]) : shiftDeriv a a P = derivative P := by sorry
