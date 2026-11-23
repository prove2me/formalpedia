-- Prove2me | Theorems.Thm_KernelRank_aeval_shifted_derivative_eq_zero_iff
-- name    : KernelRank.aeval_shifted_derivative_eq_zero_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T02:10:27.887883+00:00
-- url     : https://prove2.me/theorems/a14d7dac-2f5f-4293-af45-374a140e45b5
-- title:
--   Kernel Rank: aeval shifted derivative eq zero iff
-- statement:
--   The Kernel Rank construction uses the aeval shifted derivative eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/ComplexRank.lean#L97-L114
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/ComplexRank.lean#L97-L114

import Definitions.Def_KernelRankLean_Differential
import Definitions.Def_KernelRankLean_RealExpPoly
import Definitions.Def_KernelRankLean_ComplexRank
set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank

theorem KernelRank.aeval_shifted_derivative_eq_zero_iff (q : ℂ[X]) {P : ℂ[X]} (hP : P ≠ 0) (μ : ℂ) :
    aeval ((derivative : Module.End ℂ ℂ[X]) + μ • 1) q P = 0 ↔
      (X - C μ) ^ (P.natDegree + 1) ∣ q := by sorry
