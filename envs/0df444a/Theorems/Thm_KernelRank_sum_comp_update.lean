-- Prove2me | Theorems.Thm_KernelRank_sum_comp_update
-- name    : KernelRank.sum_comp_update
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T02:08:14.042048+00:00
-- url     : https://prove2.me/theorems/bd64badd-c2da-45fc-9b5c-c5d71583f928
-- title:
--   Kernel Rank: sum comp update
-- statement:
--   The Kernel Rank construction uses the sum comp update property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiComplexRank.lean#L355-L365
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiComplexRank.lean#L355-L365

import Definitions.Def_KernelRankLean_ComplexRank
import Definitions.Def_KernelRankLean_MultiComplexRank
set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank

theorem KernelRank.sum_comp_update {ι M : Type*} [Fintype ι] [DecidableEq ι] [AddCommMonoid M]
    (g : ℕ → M) (c : ι → ℕ) (i₀ : ι) (v : ℕ) :
    (∑ i, g (Function.update c i₀ v i)) + g (c i₀) = (∑ i, g (c i)) + g v := by sorry
