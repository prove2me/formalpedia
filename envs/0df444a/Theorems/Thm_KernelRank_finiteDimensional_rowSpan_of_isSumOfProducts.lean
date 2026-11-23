-- Prove2me | Theorems.Thm_KernelRank_finiteDimensional_rowSpan_of_isSumOfProducts
-- name    : KernelRank.finiteDimensional_rowSpan_of_isSumOfProducts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:50:24.858203+00:00
-- url     : https://prove2.me/theorems/4f61124a-cc29-4ba1-ad0c-fd8a938c202d
-- title:
--   Kernel Rank: finite Dimensional row Span of is Sum Of Products
-- statement:
--   The Kernel Rank construction uses the finite Dimensional row Span of is Sum Of Products property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/RowSpan.lean#L56-L60
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/RowSpan.lean#L56-L60

import Definitions.Def_KernelRankLean_Defs
import Definitions.Def_KernelRankLean_RowSpan
set_option autoImplicit true
open KernelRank
variable {𝕜 α : Type*}
variable [Field 𝕜]

theorem KernelRank.finiteDimensional_rowSpan_of_isSumOfProducts {K : (Fin 2 → α) → 𝕜} {N : ℕ}
    (hK : IsSumOfProducts K N) : FiniteDimensional 𝕜 (rowSpan K) := by sorry
