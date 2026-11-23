-- Prove2me | Theorems.Thm_KernelRank_finrank_rowSpan_le_of_isSumOfProducts
-- name    : KernelRank.finrank_rowSpan_le_of_isSumOfProducts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:50:25.45656+00:00
-- url     : https://prove2.me/theorems/c8e7a1bc-344e-48a8-bdf4-7f6ca982dd17
-- title:
--   Kernel Rank: finrank row Span le of is Sum Of Products
-- statement:
--   The Kernel Rank construction uses the finrank row Span le of is Sum Of Products property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/RowSpan.lean#L62-L70
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/RowSpan.lean#L62-L70

import Definitions.Def_KernelRankLean_Defs
import Definitions.Def_KernelRankLean_RowSpan
set_option autoImplicit true
open KernelRank
variable {𝕜 α : Type*}
variable [Field 𝕜]

theorem KernelRank.finrank_rowSpan_le_of_isSumOfProducts {K : (Fin 2 → α) → 𝕜} {N : ℕ}
    (hK : IsSumOfProducts K N) : Module.finrank 𝕜 (rowSpan K) ≤ N := by sorry
