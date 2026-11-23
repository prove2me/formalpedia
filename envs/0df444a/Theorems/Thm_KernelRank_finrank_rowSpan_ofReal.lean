-- Prove2me | Theorems.Thm_KernelRank_finrank_rowSpan_ofReal
-- name    : KernelRank.finrank_rowSpan_ofReal
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T01:51:56.775039+00:00
-- url     : https://prove2.me/theorems/24605d0c-36a9-4d3b-bcdc-b41347c30596
-- title:
--   Kernel Rank: finrank row Span of Real
-- statement:
--   The real row span and the complex row span have the same finite dimension.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Complexification.lean#L85-L101
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Complexification.lean#L85-L101

import Definitions.Def_KernelRankLean_RowSpan
import Definitions.Def_KernelRankLean_Complexification
set_option autoImplicit true
open KernelRank
variable {α : Type*}

theorem KernelRank.finrank_rowSpan_ofReal (K : (Fin 2 → α) → ℝ)
    [FiniteDimensional ℂ (rowSpan (fun z => (K z : ℂ)))] :
    Module.finrank ℝ (rowSpan K) =
      Module.finrank ℂ (rowSpan (fun z => (K z : ℂ))) := by sorry
