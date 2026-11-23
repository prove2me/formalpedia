-- Prove2me | Theorems.Thm_KernelRank_expPoly_add
-- name    : KernelRank.expPoly_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:52:19.996013+00:00
-- url     : https://prove2.me/theorems/2443dd58-da2e-47fd-8c6c-e376c751711c
-- title:
--   Kernel Rank: exp Poly add
-- statement:
--   The Kernel Rank construction uses the exp Poly add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/ExpPoly.lean#L24-L26
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/ExpPoly.lean#L24-L26

import Mathlib
import Definitions.Def_KernelRankLean_ExpPoly
set_option autoImplicit true
open Complex Polynomial
open KernelRank

theorem KernelRank.expPoly_add (P Q : ℂ[X]) (μ : ℂ) (u : ℝ) :
    expPoly (P + Q) μ u = expPoly P μ u + expPoly Q μ u := by sorry
