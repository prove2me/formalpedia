-- Prove2me | Theorems.Thm_KernelRank_separableRank_radial_gaussian_eq_iff
-- name    : KernelRank.separableRank_radial_gaussian_eq_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T02:41:50.325601+00:00
-- url     : https://prove2.me/theorems/768f978d-be09-41c6-9760-4399a52ede4f
-- title:
--   Kernel Rank: separable Rank radial gaussian eq iff
-- statement:
--   **Exact `d`-D real multi-Gaussian rank (`d ≥ 2`).** Among multi-Gaussian radial kernels on
--   `ℝ^d`, the `d`-way separable rank equals `N` if and only if the Gaussian representation has
--   `gaussianTotalCost d cs = N` (`1` per real Gaussian, `d` per nonreal conjugate-pair Gaussian).
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Main.lean#L146-L159
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Main.lean#L146-L159

import Definitions.Def_KernelRankLean_Necessity
import Definitions.Def_KernelRankLean_MultiComplexRank
import Definitions.Def_KernelRankLean_MultiRealRank
import Definitions.Def_KernelRankLean_Main
set_option autoImplicit true
open Complex Polynomial Filter Topology
open KernelRank

theorem KernelRank.separableRank_radial_gaussian_eq_iff {d : ℕ} (hd : 2 ≤ d) (φ : ℝ → ℝ)
    (hφ : ∃ cs : List Component, IsGaussianRepresentation cs ∧ ∀ s, 0 ≤ s → φ s = profile cs s)
    (N : ℕ) :
    separableRank (fun x : Fin d → ℝ => φ (∑ j, x j ^ 2)) = N ↔
      ∃ cs : List Component, IsGaussianRepresentation cs ∧
        (∀ s, 0 ≤ s → φ s = profile cs s) ∧ gaussianTotalCost d cs = N := by sorry
