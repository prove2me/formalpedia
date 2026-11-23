-- Prove2me | Theorems.Thm_KernelRank_sum_update_nat
-- name    : KernelRank.sum_update_nat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T02:08:33.527815+00:00
-- url     : https://prove2.me/theorems/f0f1ae8b-bca2-4839-a179-6fcf8e58b267
-- title:
--   Kernel Rank: sum update nat
-- statement:
--   The Kernel Rank construction uses the sum update nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiComplexRank.lean#L367-L369
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiComplexRank.lean#L367-L369

import Definitions.Def_KernelRankLean_ComplexRank
import Definitions.Def_KernelRankLean_MultiComplexRank
set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank

theorem KernelRank.sum_update_nat {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℕ) (i₀ : ι) (v : ℕ) :
    (∑ i, Function.update c i₀ v i) + c i₀ = (∑ i, c i) + v := by sorry
