-- Prove2me | Theorems.Thm_KernelRank_separableRank_radial_eq_hankel
-- name    : KernelRank.separableRank_radial_eq_hankel
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T01:49:56.397943+00:00
-- url     : https://prove2.me/theorems/f02a049e-78a0-44ed-bb52-01f42475de25
-- title:
--   Kernel Rank: separable Rank radial eq hankel
-- statement:
--   Squaring maps `ℝ` onto `[0, ∞)`, so the `d`-D radial kernel `x ↦ φ (∑ i, x i ^ 2)` has the
--   same separable rank as the `d`-D Hankel kernel `s ↦ φ (∑ i, s i)` on `[0, ∞)^d`.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Translations.lean#L26-L33
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Translations.lean#L26-L33

import Definitions.Def_KernelRankLean_RowSpan
import Definitions.Def_KernelRankLean_Translations
set_option autoImplicit true
open NNReal
open KernelRank

theorem KernelRank.separableRank_radial_eq_hankel {𝕜 : Type*} [CommSemiring 𝕜] (d : ℕ) (φ : ℝ → 𝕜) :
    separableRank (fun x : Fin d → ℝ => φ (∑ i, x i ^ 2)) =
      separableRank (fun s : Fin d → ℝ≥0 => φ (∑ i, (s i : ℝ))) := by sorry
