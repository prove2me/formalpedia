-- Prove2me | Theorems.Thm_KernelRank_separableRank_radial_two_eq_finrank
-- name    : KernelRank.separableRank_radial_two_eq_finrank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:56:46.146141+00:00
-- url     : https://prove2.me/theorems/6234ecbf-911a-4735-86de-2a5f61114fa1
-- title:
--   Kernel Rank: separable Rank radial two eq finrank
-- statement:
--   The separable rank of a 2-D radial kernel is the dimension of the span of its profile's
--   translates on `[0, ∞)`, when that is finite.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Translations.lean#L84-L90
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Translations.lean#L84-L90

import Definitions.Def_KernelRankLean_RowSpan
import Definitions.Def_KernelRankLean_Translations
set_option autoImplicit true
open NNReal
open KernelRank

theorem KernelRank.separableRank_radial_two_eq_finrank {𝕜 : Type*} [Field 𝕜] (φ : ℝ → 𝕜)
    [FiniteDimensional 𝕜 (translateSpan φ)] :
    separableRank (fun x : Fin 2 → ℝ => φ (∑ i, x i ^ 2)) =
      Module.finrank 𝕜 (translateSpan φ) := by sorry
