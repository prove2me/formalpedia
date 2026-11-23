-- Prove2me | Theorems.Thm_KernelRank_finiteDimensional_rowSpan_ofReal
-- name    : KernelRank.finiteDimensional_rowSpan_ofReal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:52:01.327648+00:00
-- url     : https://prove2.me/theorems/2475b24e-73b8-4f64-82c2-d538bf17e8ab
-- title:
--   Kernel Rank: finite Dimensional row Span of Real
-- statement:
--   Finite-dimensionality of the complex row span implies it for the real row span.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Complexification.lean#L71-L82
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Complexification.lean#L71-L82

import Definitions.Def_KernelRankLean_RowSpan
import Definitions.Def_KernelRankLean_Complexification
set_option autoImplicit true
open KernelRank
variable {α : Type*}

theorem KernelRank.finiteDimensional_rowSpan_ofReal (K : (Fin 2 → α) → ℝ)
    [FiniteDimensional ℂ (rowSpan (fun z => (K z : ℂ)))] :
    FiniteDimensional ℝ (rowSpan K) := by sorry
