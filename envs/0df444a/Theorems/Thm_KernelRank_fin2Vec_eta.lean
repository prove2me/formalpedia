-- Prove2me | Theorems.Thm_KernelRank_fin2Vec_eta
-- name    : KernelRank.fin2Vec_eta
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:51:55.96314+00:00
-- url     : https://prove2.me/theorems/8de5c495-a85f-4700-b65a-18e13f5d3716
-- title:
--   Kernel Rank: fin2 Vec eta
-- statement:
--   The Kernel Rank construction uses the fin2 Vec eta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/RowSpan.lean#L26-L30
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/RowSpan.lean#L26-L30

import Definitions.Def_KernelRankLean_Defs
import Definitions.Def_KernelRankLean_RowSpan
set_option autoImplicit true
open KernelRank
variable {𝕜 α : Type*}

theorem KernelRank.fin2Vec_eta (z : Fin 2 → α) : fin2Vec (z 0) (z 1) = z := by sorry
