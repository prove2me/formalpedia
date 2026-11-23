-- Prove2me | Theorems.Thm_KernelRank_fin2Vec_zero
-- name    : KernelRank.fin2Vec_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:49:08.114299+00:00
-- url     : https://prove2.me/theorems/359b8247-a42c-4b59-ac27-a2457b7c07d5
-- title:
--   Kernel Rank: fin2 Vec zero
-- statement:
--   The Kernel Rank construction uses the fin2 Vec zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/RowSpan.lean#L22-L22
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/RowSpan.lean#L22-L22

import Definitions.Def_KernelRankLean_Defs
import Definitions.Def_KernelRankLean_RowSpan
set_option autoImplicit true
open KernelRank
variable {𝕜 α : Type*}

theorem KernelRank.fin2Vec_zero (x y : α) : fin2Vec x y 0 = x := by sorry

attribute [defeq] KernelRank.fin2Vec_zero
