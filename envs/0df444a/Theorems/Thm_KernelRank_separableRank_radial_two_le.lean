-- Prove2me | Theorems.Thm_KernelRank_separableRank_radial_two_le
-- name    : KernelRank.separableRank_radial_two_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:51:56.39993+00:00
-- url     : https://prove2.me/theorems/fd510ab3-d127-436e-8a6a-aa4da5249468
-- title:
--   Kernel Rank: separable Rank radial two le
-- statement:
--   Restricting a `d`-D radial kernel (`d ≥ 2`) to its first two coordinates bounds the 2-D
--   radial rank by the `d`-D radial rank.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Translations.lean#L37-L65
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Translations.lean#L37-L65

import Definitions.Def_KernelRankLean_RowSpan
import Definitions.Def_KernelRankLean_Translations
set_option autoImplicit true
open NNReal
open KernelRank

theorem KernelRank.separableRank_radial_two_le {𝕜 : Type*} [CommSemiring 𝕜] {d : ℕ} (hd : 2 ≤ d)
    (φ : ℝ → 𝕜) :
    separableRank (fun y : Fin 2 → ℝ => φ (∑ k, y k ^ 2)) ≤
      separableRank (fun x : Fin d → ℝ => φ (∑ i, x i ^ 2)) := by sorry
