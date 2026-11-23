-- Prove2me | Theorems.Thm_KernelRank_separableRank_radial_two_lt_top_iff
-- name    : KernelRank.separableRank_radial_two_lt_top_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:52:12.077086+00:00
-- url     : https://prove2.me/theorems/481a2e0b-5f68-4e3f-b837-e3b1bd6a25d2
-- title:
--   Kernel Rank: separable Rank radial two lt top iff
-- statement:
--   A 2-D radial kernel has finite separable rank iff the translates of its profile on `[0, ∞)`
--   span a finite-dimensional space.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Translations.lean#L77-L80
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Translations.lean#L77-L80

import Definitions.Def_KernelRankLean_RowSpan
import Definitions.Def_KernelRankLean_Translations
set_option autoImplicit true
open NNReal
open KernelRank

theorem KernelRank.separableRank_radial_two_lt_top_iff {𝕜 : Type*} [Field 𝕜] (φ : ℝ → 𝕜) :
    separableRank (fun x : Fin 2 → ℝ => φ (∑ i, x i ^ 2)) < ⊤ ↔
      FiniteDimensional 𝕜 (translateSpan φ) := by sorry
