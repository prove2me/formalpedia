-- Prove2me | Theorems.Thm_KernelRank_span_range_eq_top_of_dual
-- name    : KernelRank.span_range_eq_top_of_dual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T02:09:31.807257+00:00
-- url     : https://prove2.me/theorems/27a62d73-8fbc-4129-88d9-9d5dfab2080a
-- title:
--   Kernel Rank: span range eq top of dual
-- statement:
--   If every linear functional vanishing on `Set.range v` is zero, then `Set.range v` spans `V`.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiComplexRank.lean#L320-L329
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiComplexRank.lean#L320-L329

import Definitions.Def_KernelRankLean_ComplexRank
import Definitions.Def_KernelRankLean_MultiComplexRank
set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank

theorem KernelRank.span_range_eq_top_of_dual {𝕜 α V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
    {v : α → V} (h : ∀ L : V →ₗ[𝕜] 𝕜, (∀ s, L (v s) = 0) → L = 0) :
    Submodule.span 𝕜 (Set.range v) = ⊤ := by sorry
