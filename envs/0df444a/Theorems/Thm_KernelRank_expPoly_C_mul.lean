-- Prove2me | Theorems.Thm_KernelRank_expPoly_C_mul
-- name    : KernelRank.expPoly_C_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:52:26.109468+00:00
-- url     : https://prove2.me/theorems/42143240-3cda-4eb1-b57a-a43f2b228643
-- title:
--   Kernel Rank: exp Poly C mul
-- statement:
--   The Kernel Rank construction uses the exp Poly C mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/ExpPoly.lean#L28-L30
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/ExpPoly.lean#L28-L30

import Mathlib
import Definitions.Def_KernelRankLean_ExpPoly
set_option autoImplicit true
open Complex Polynomial
open KernelRank

theorem KernelRank.expPoly_C_mul (c : ℂ) (P : ℂ[X]) (μ : ℂ) (u : ℝ) :
    expPoly (C c * P) μ u = c * expPoly P μ u := by sorry
