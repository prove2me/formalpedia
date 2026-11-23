-- Prove2me | Theorems.Thm_KernelRank_hasDerivAt_expPoly
-- name    : KernelRank.hasDerivAt_expPoly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:52:35.003546+00:00
-- url     : https://prove2.me/theorems/a33881a7-7cba-4c19-adce-8b8fc7d5851f
-- title:
--   Kernel Rank: has Deriv At exp Poly
-- statement:
--   The Kernel Rank construction uses the has Deriv At exp Poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/ExpPoly.lean#L32-L42
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/ExpPoly.lean#L32-L42

import Mathlib
import Definitions.Def_KernelRankLean_ExpPoly
set_option autoImplicit true
open Complex Polynomial
open KernelRank

theorem KernelRank.hasDerivAt_expPoly (P : ℂ[X]) (μ : ℂ) (u : ℝ) :
    HasDerivAt (expPoly P μ) (expPoly (derivative P + C μ * P) μ u) u := by sorry
