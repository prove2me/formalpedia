-- Prove2me | Theorems.Thm_KernelRank_fin2Vec_one
-- name    : KernelRank.fin2Vec_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:49:08.989075+00:00
-- url     : https://prove2.me/theorems/21e5139f-5a91-410e-87cf-ec1af4109739
-- title:
--   Kernel Rank: fin2 Vec one
-- statement:
--   The Kernel Rank construction uses the fin2 Vec one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/RowSpan.lean#L24-L24
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/RowSpan.lean#L24-L24

import Definitions.Def_KernelRankLean_Defs
import Definitions.Def_KernelRankLean_RowSpan
set_option autoImplicit true
open KernelRank
variable {𝕜 α : Type*}

theorem KernelRank.fin2Vec_one (x y : α) : fin2Vec x y 1 = y := by sorry

attribute [defeq] KernelRank.fin2Vec_one
