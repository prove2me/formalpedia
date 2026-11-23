-- Prove2me | Theorems.Thm_KernelRank_row_mem_rowSpan
-- name    : KernelRank.row_mem_rowSpan
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T01:49:43.323591+00:00
-- url     : https://prove2.me/theorems/056067b1-76f8-4ced-a184-2b08b617145f
-- title:
--   Kernel Rank: row mem row Span
-- statement:
--   The Kernel Rank construction uses the row mem row Span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/RowSpan.lean#L38-L40
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/RowSpan.lean#L38-L40

import Definitions.Def_KernelRankLean_Defs
import Definitions.Def_KernelRankLean_RowSpan
set_option autoImplicit true
open KernelRank
variable {𝕜 α : Type*}
variable [Field 𝕜]

theorem KernelRank.row_mem_rowSpan (K : (Fin 2 → α) → 𝕜) (y : α) :
    (fun x => K (fin2Vec x y)) ∈ rowSpan K := by sorry
