-- Prove2me | Theorems.Thm_KernelRank_rowSpan_le_of_isSumOfProducts
-- name    : KernelRank.rowSpan_le_of_isSumOfProducts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:51:42.613615+00:00
-- url     : https://prove2.me/theorems/cd66f0cc-d17e-4e95-8703-1ec42e9929ec
-- title:
--   Kernel Rank: row Span le of is Sum Of Products
-- statement:
--   A sum of `N` products has a row span inside the span of its `N` functions of coordinate `0`.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/RowSpan.lean#L43-L54
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/RowSpan.lean#L43-L54

import Definitions.Def_KernelRankLean_Defs
import Definitions.Def_KernelRankLean_RowSpan
set_option autoImplicit true
open KernelRank
variable {𝕜 α : Type*}
variable [Field 𝕜]

theorem KernelRank.rowSpan_le_of_isSumOfProducts {K : (Fin 2 → α) → 𝕜} {N : ℕ}
    {f : Fin N → Fin 2 → α → 𝕜}
    (hK : ∀ z, K z = ∑ n, ∏ i : Fin 2, f n i (z i)) :
    rowSpan K ≤ Submodule.span 𝕜 (Set.range fun n => f n 0) := by sorry
