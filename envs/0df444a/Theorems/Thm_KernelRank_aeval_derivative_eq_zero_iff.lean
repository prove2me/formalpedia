-- Prove2me | Theorems.Thm_KernelRank_aeval_derivative_eq_zero_iff
-- name    : KernelRank.aeval_derivative_eq_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T02:09:46.483643+00:00
-- url     : https://prove2.me/theorems/166cf37f-904c-4797-9cfd-552930e2b2f6
-- title:
--   Kernel Rank: aeval derivative eq zero iff
-- statement:
--   The Kernel Rank construction uses the aeval derivative eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/ComplexRank.lean#L86-L95
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/ComplexRank.lean#L86-L95

import Definitions.Def_KernelRankLean_Differential
import Definitions.Def_KernelRankLean_RealExpPoly
import Definitions.Def_KernelRankLean_ComplexRank
set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank

theorem KernelRank.aeval_derivative_eq_zero_iff (q : ℂ[X]) {P : ℂ[X]} (hP : P ≠ 0) :
    aeval (derivative : Module.End ℂ ℂ[X]) q P = 0 ↔
      X ^ (P.natDegree + 1) ∣ q := by sorry
