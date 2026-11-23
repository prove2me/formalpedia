-- Prove2me | Theorems.Thm_KernelRank_eval_ofReal_conjPoly
-- name    : KernelRank.eval_ofReal_conjPoly
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T02:01:21.02711+00:00
-- url     : https://prove2.me/theorems/8ceee293-54ca-4aff-8580-b0d281437bc1
-- title:
--   Kernel Rank: eval of Real conj Poly
-- statement:
--   The Kernel Rank construction uses the eval of Real conj Poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/RealExpPoly.lean#L36-L38
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/RealExpPoly.lean#L36-L38

import Definitions.Def_KernelRankLean_ExpPoly
import Definitions.Def_KernelRankLean_RealExpPoly
set_option autoImplicit true
open Complex Polynomial
open KernelRank

theorem KernelRank.eval_ofReal_conjPoly (A : ℂ[X]) (u : ℝ) :
    (conjPoly A).eval (u : ℂ) = starRingEnd ℂ (A.eval (u : ℂ)) := by sorry
