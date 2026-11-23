-- Prove2me | Theorems.Thm_KernelRank_differentialOperator_sum_expPoly
-- name    : KernelRank.differentialOperator_sum_expPoly
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T02:11:07.81352+00:00
-- url     : https://prove2.me/theorems/6428f07c-d9b1-40f1-aa6d-7a7f31cd7d1a
-- title:
--   Kernel Rank: differential Operator sum exp Poly
-- statement:
--   The Kernel Rank construction uses the differential Operator sum exp Poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/ComplexRank.lean#L136-L143
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/ComplexRank.lean#L136-L143

import Definitions.Def_KernelRankLean_Differential
import Definitions.Def_KernelRankLean_RealExpPoly
import Definitions.Def_KernelRankLean_ComplexRank
set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank

theorem KernelRank.differentialOperator_sum_expPoly {ι : Type*} [Fintype ι]
    (q : ℂ[X]) (P : ι → ℂ[X]) (rate : ι → ℂ) {t : ℝ} (ht : 0 ≤ t) :
    differentialOperator q (fun u => ∑ i, expPoly (P i) (rate i) u) t =
      ∑ i, expPoly (aeval ((derivative : Module.End ℂ ℂ[X]) + rate i • 1) q (P i)) (rate i) t := by sorry
