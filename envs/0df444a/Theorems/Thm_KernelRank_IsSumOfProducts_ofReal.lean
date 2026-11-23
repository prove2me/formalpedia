-- Prove2me | Theorems.Thm_KernelRank_IsSumOfProducts_ofReal
-- name    : KernelRank.IsSumOfProducts.ofReal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:50:46.585791+00:00
-- url     : https://prove2.me/theorems/94fc0ce1-9ca7-4aa0-97ff-47d0c1030e24
-- title:
--   Is Sum Of Products: of Real
-- statement:
--   A real product decomposition can be read as a complex product decomposition, in any number of
--   coordinates.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Complexification.lean#L35-L40
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Complexification.lean#L35-L40

import Definitions.Def_KernelRankLean_RowSpan
import Definitions.Def_KernelRankLean_Complexification
set_option autoImplicit true
open KernelRank

theorem KernelRank.IsSumOfProducts.ofReal {ι : Type*} [Fintype ι] {X : ι → Type*} {K : (∀ i, X i) → ℝ}
    {N : ℕ} (hK : IsSumOfProducts K N) :
    IsSumOfProducts (fun x => (K x : ℂ)) N := by sorry
