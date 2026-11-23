-- Prove2me | Theorems.Thm_KernelRank_isSumOfProducts_finrank_rowSpan
-- name    : KernelRank.isSumOfProducts_finrank_rowSpan
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T01:49:25.00645+00:00
-- url     : https://prove2.me/theorems/bb86cb5b-00a0-4de9-858e-09826e4311b3
-- title:
--   Kernel Rank: is Sum Of Products finrank row Span
-- statement:
--   A finite-dimensional row span gives a sum of `finrank` products: expand each row in a basis.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/RowSpan.lean#L73-L86
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/RowSpan.lean#L73-L86

import Definitions.Def_KernelRankLean_Defs
import Definitions.Def_KernelRankLean_RowSpan
set_option autoImplicit true
open KernelRank
variable {𝕜 α : Type*}
variable [Field 𝕜]

theorem KernelRank.isSumOfProducts_finrank_rowSpan (K : (Fin 2 → α) → 𝕜)
    [FiniteDimensional 𝕜 (rowSpan K)] :
    IsSumOfProducts K (Module.finrank 𝕜 (rowSpan K)) := by sorry
