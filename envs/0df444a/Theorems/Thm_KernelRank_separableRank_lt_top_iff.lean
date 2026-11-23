-- Prove2me | Theorems.Thm_KernelRank_separableRank_lt_top_iff
-- name    : KernelRank.separableRank_lt_top_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:56:26.219314+00:00
-- url     : https://prove2.me/theorems/64c1c95c-7047-41c4-874c-6a13798ded3b
-- title:
--   Kernel Rank: separable Rank lt top iff
-- statement:
--   In two coordinates, the separable rank is finite iff the row span is finite-dimensional.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/RowSpan.lean#L89-L97
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/RowSpan.lean#L89-L97

import Definitions.Def_KernelRankLean_Defs
import Definitions.Def_KernelRankLean_RowSpan
set_option autoImplicit true
open KernelRank
variable {𝕜 α : Type*}
variable [Field 𝕜]

theorem KernelRank.separableRank_lt_top_iff (K : (Fin 2 → α) → 𝕜) :
    separableRank K < ⊤ ↔ FiniteDimensional 𝕜 (rowSpan K) := by sorry
