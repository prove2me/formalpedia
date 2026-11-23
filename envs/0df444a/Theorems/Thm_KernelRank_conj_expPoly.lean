-- Prove2me | Theorems.Thm_KernelRank_conj_expPoly
-- name    : KernelRank.conj_expPoly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T02:01:25.461524+00:00
-- url     : https://prove2.me/theorems/ee5960db-1012-4c75-b2d4-625c7c6a5041
-- title:
--   Kernel Rank: conj exp Poly
-- statement:
--   The Kernel Rank construction uses the conj exp Poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/RealExpPoly.lean#L40-L42
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/RealExpPoly.lean#L40-L42

import Definitions.Def_KernelRankLean_ExpPoly
import Definitions.Def_KernelRankLean_RealExpPoly
set_option autoImplicit true
open Complex Polynomial
open KernelRank

theorem KernelRank.conj_expPoly (A : ℂ[X]) (μ : ℂ) (u : ℝ) :
    starRingEnd ℂ (expPoly A μ u) = expPoly (conjPoly A) (starRingEnd ℂ μ) u := by sorry
