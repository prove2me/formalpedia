-- Prove2me | Theorems.Thm_KernelRank_ofReal_mem_rowSpan
-- name    : KernelRank.ofReal_mem_rowSpan
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:57:29.928647+00:00
-- url     : https://prove2.me/theorems/d05bc9c6-9315-4593-89e3-523b3874d53a
-- title:
--   Kernel Rank: of Real mem row Span
-- statement:
--   Complexifying a real row combination gives a complex row combination.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Complexification.lean#L53-L68
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Complexification.lean#L53-L68

import Definitions.Def_KernelRankLean_RowSpan
import Definitions.Def_KernelRankLean_Complexification
set_option autoImplicit true
open KernelRank
variable {α : Type*}

theorem KernelRank.ofReal_mem_rowSpan {K : (Fin 2 → α) → ℝ} {f : α → ℝ} (hf : f ∈ rowSpan K) :
    (fun x => (f x : ℂ)) ∈ rowSpan (fun z => (K z : ℂ)) := by sorry
