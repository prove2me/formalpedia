-- Prove2me | Theorems.Thm_KernelRank_separableRank_eq_finrank_rowSpan
-- name    : KernelRank.separableRank_eq_finrank_rowSpan
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:51:50.697574+00:00
-- url     : https://prove2.me/theorems/2b2fb68f-fc79-4cbd-a2cb-006cc24f195f
-- title:
--   Kernel Rank: separable Rank eq finrank row Span
-- statement:
--   With a finite-dimensional row span, the two-coordinate separable rank is its dimension.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/RowSpan.lean#L100-L104
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/RowSpan.lean#L100-L104

import Definitions.Def_KernelRankLean_Defs
import Definitions.Def_KernelRankLean_RowSpan
set_option autoImplicit true
open KernelRank
variable {𝕜 α : Type*}
variable [Field 𝕜]

theorem KernelRank.separableRank_eq_finrank_rowSpan (K : (Fin 2 → α) → 𝕜)
    [FiniteDimensional 𝕜 (rowSpan K)] :
    separableRank K = Module.finrank 𝕜 (rowSpan K) := by sorry
