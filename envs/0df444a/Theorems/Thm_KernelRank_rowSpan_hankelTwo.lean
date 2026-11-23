-- Prove2me | Theorems.Thm_KernelRank_rowSpan_hankelTwo
-- name    : KernelRank.rowSpan_hankelTwo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:49:55.240457+00:00
-- url     : https://prove2.me/theorems/2bbaeb4a-94d3-44c9-a118-bbbc26e1e2ef
-- title:
--   Kernel Rank: row Span hankel Two
-- statement:
--   The row span of the 2-D Hankel kernel `(s₀, s₁) ↦ φ (s₀ + s₁)` is `translateSpan φ`.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Translations.lean#L68-L73
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Translations.lean#L68-L73

import Definitions.Def_KernelRankLean_RowSpan
import Definitions.Def_KernelRankLean_Translations
set_option autoImplicit true
open NNReal
open KernelRank

theorem KernelRank.rowSpan_hankelTwo {𝕜 : Type*} [Field 𝕜] (φ : ℝ → 𝕜) :
    rowSpan (fun s : Fin 2 → ℝ≥0 => φ (∑ i, (s i : ℝ))) = translateSpan φ := by sorry
