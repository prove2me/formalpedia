-- Prove2me | Theorems.Thm_KernelRank_finrank_translateSpan_sum_expPoly
-- name    : KernelRank.finrank_translateSpan_sum_expPoly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T02:11:59.212327+00:00
-- url     : https://prove2.me/theorems/f3227ab7-ceee-4483-bd31-3ae2fec8892d
-- title:
--   Kernel Rank: finrank translate Span sum exp Poly
-- statement:
--   The dimension of a complex exponential polynomial's translate span is its total multiplicity.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/ComplexRank.lean#L187-L226
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/ComplexRank.lean#L187-L226

import Definitions.Def_KernelRankLean_Differential
import Definitions.Def_KernelRankLean_RealExpPoly
import Definitions.Def_KernelRankLean_ComplexRank
set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank

theorem KernelRank.finrank_translateSpan_sum_expPoly {ι : Type*} [Fintype ι] {rate : ι → ℂ}
    (hinj : Function.Injective rate) (P : ι → ℂ[X]) (hP : ∀ i, P i ≠ 0) :
    FiniteDimensional ℂ (translateSpan (fun t => ∑ i, expPoly (P i) (rate i) t)) ∧
      Module.finrank ℂ (translateSpan (fun t => ∑ i, expPoly (P i) (rate i) t)) =
        ∑ i, ((P i).natDegree + 1) := by sorry
