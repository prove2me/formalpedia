-- Prove2me | Theorems.Thm_KernelRank_truncMultilinearMap_apply
-- name    : KernelRank.truncMultilinearMap_apply
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T02:15:24.057795+00:00
-- url     : https://prove2.me/theorems/6bef286a-6197-43bb-91dc-abb738bde360
-- title:
--   Kernel Rank: trunc Multilinear Map apply
-- statement:
--   The Kernel Rank construction uses the trunc Multilinear Map apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiComplexRank.lean#L915-L918
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiComplexRank.lean#L915-L918

import Definitions.Def_KernelRankLean_ComplexRank
import Definitions.Def_KernelRankLean_MultiComplexRank
set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank

theorem KernelRank.truncMultilinearMap_apply {ι : Type*} [Fintype ι] (d : ℕ) (m₀ c : ι → ℕ)
    (w : ι → ℕ → ℂ) (u : Fin d → CoeffSpace m₀) :
    truncMultilinearMap d m₀ c w u = truncForm d m₀ c w u := by sorry
