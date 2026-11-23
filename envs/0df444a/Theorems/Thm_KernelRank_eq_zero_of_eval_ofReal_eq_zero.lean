-- Prove2me | Theorems.Thm_KernelRank_eq_zero_of_eval_ofReal_eq_zero
-- name    : KernelRank.eq_zero_of_eval_ofReal_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T02:00:53.778291+00:00
-- url     : https://prove2.me/theorems/006e1de8-5641-4548-8ab8-3d02a035589e
-- title:
--   Kernel Rank: eq zero of eval of Real eq zero
-- statement:
--   A polynomial vanishing on `u > 0` is zero.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/ExpPoly.lean#L102-L107
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/ExpPoly.lean#L102-L107

import Mathlib
import Definitions.Def_KernelRankLean_ExpPoly
set_option autoImplicit true
open Complex Polynomial
open KernelRank

theorem KernelRank.eq_zero_of_eval_ofReal_eq_zero {P : ℂ[X]} (h : ∀ u : ℝ, 0 < u → P.eval (u : ℂ) = 0) :
    P = 0 := by sorry
