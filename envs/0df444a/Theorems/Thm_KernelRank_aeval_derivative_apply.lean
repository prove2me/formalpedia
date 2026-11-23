-- Prove2me | Theorems.Thm_KernelRank_aeval_derivative_apply
-- name    : KernelRank.aeval_derivative_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T02:09:59.618491+00:00
-- url     : https://prove2.me/theorems/dfc0fea6-f7f2-4f7c-b5a7-ae36d40bfa46
-- title:
--   Kernel Rank: aeval derivative apply
-- statement:
--   The Kernel Rank construction uses the aeval derivative apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/ComplexRank.lean#L62-L84
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/ComplexRank.lean#L62-L84

import Definitions.Def_KernelRankLean_Differential
import Definitions.Def_KernelRankLean_RealExpPoly
import Definitions.Def_KernelRankLean_ComplexRank
set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank

theorem KernelRank.aeval_derivative_apply (q P : ℂ[X]) :
    aeval (derivative : Module.End ℂ ℂ[X]) q P =
      ∑ k : Fin (P.natDegree + 1),
        (q.coeff k * (k.val.factorial : ℂ)) • hasseDeriv k P := by sorry
