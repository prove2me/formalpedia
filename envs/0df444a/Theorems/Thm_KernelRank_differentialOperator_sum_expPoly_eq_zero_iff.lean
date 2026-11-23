-- Prove2me | Theorems.Thm_KernelRank_differentialOperator_sum_expPoly_eq_zero_iff
-- name    : KernelRank.differentialOperator_sum_expPoly_eq_zero_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T02:08:01.61885+00:00
-- url     : https://prove2.me/theorems/64d5f6da-901a-4533-8c16-d4024fbc7f75
-- title:
--   Kernel Rank: differential Operator sum exp Poly eq zero iff
-- statement:
--   A differential polynomial annihilates the sum exactly when all rate factors divide it.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/ComplexRank.lean#L161-L184
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/ComplexRank.lean#L161-L184

import Definitions.Def_KernelRankLean_Differential
import Definitions.Def_KernelRankLean_RealExpPoly
import Definitions.Def_KernelRankLean_ComplexRank
set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank

theorem KernelRank.differentialOperator_sum_expPoly_eq_zero_iff {ι : Type*} [Fintype ι]
    (P : ι → ℂ[X]) (rate : ι → ℂ) (hinj : Function.Injective rate)
    (hP : ∀ i, P i ≠ 0) (q : ℂ[X]) :
    (∀ t, 0 ≤ t → differentialOperator q (fun u => ∑ i, expPoly (P i) (rate i) u) t = 0) ↔
      expPolyAnnihilator P rate ∣ q := by sorry
