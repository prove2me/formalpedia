-- Prove2me | Theorems.Thm_KernelRank_separableRank_ofReal_le
-- name    : KernelRank.separableRank_ofReal_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:57:15.334746+00:00
-- url     : https://prove2.me/theorems/9a2cccb6-43e2-4caf-9cb6-3680bfe366db
-- title:
--   Kernel Rank: separable Rank of Real le
-- statement:
--   Complexifying never increases separable rank in any dimension.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Complexification.lean#L43-L46
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Complexification.lean#L43-L46

import Definitions.Def_KernelRankLean_RowSpan
import Definitions.Def_KernelRankLean_Complexification
set_option autoImplicit true
open KernelRank

theorem KernelRank.separableRank_ofReal_le {ι : Type*} [Fintype ι] {X : ι → Type*}
    (K : (∀ i, X i) → ℝ) :
    separableRank (fun x => (K x : ℂ)) ≤ separableRank K := by sorry
