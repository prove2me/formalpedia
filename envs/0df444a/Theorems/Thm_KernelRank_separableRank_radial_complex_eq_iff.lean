-- Prove2me | Theorems.Thm_KernelRank_separableRank_radial_complex_eq_iff
-- name    : KernelRank.separableRank_radial_complex_eq_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T02:17:02.172689+00:00
-- url     : https://prove2.me/theorems/4b69afe7-f7b3-42ad-b57f-746bf567317e
-- title:
--   Kernel Rank: separable Rank radial complex eq iff
-- statement:
--   **Exact `d`-D complex radial rank (`d ≥ 2`).** A complex radial kernel on `ℝ^d`, with profile
--   continuous on `[0, ∞)`, has `d`-way separable rank `N` if and only if its profile agrees on
--   `[0, ∞)` with a finite sum of nonzero exponential polynomials at distinct rates whose `(d - 1)`-
--   weighted degrees sum to `N`.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Main.lean#L94-L141
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Main.lean#L94-L141

import Definitions.Def_KernelRankLean_Necessity
import Definitions.Def_KernelRankLean_MultiComplexRank
import Definitions.Def_KernelRankLean_MultiRealRank
import Definitions.Def_KernelRankLean_Main
set_option autoImplicit true
open Complex Polynomial Filter Topology
open KernelRank
open scoped Classical

theorem KernelRank.separableRank_radial_complex_eq_iff {d : ℕ} (hd : 2 ≤ d)
    (ψ : ℝ → ℂ) (hψ : ContinuousOn ψ (Set.Ici 0)) (N : ℕ) :
    separableRank (fun x : Fin d → ℝ => ψ (∑ j, x j ^ 2)) = N ↔
      ∃ (S : Finset ℂ) (P : ℂ → ℂ[X]),
        (∀ μ ∈ S, P μ ≠ 0) ∧
        (∀ s, 0 ≤ s → ψ s = ∑ μ ∈ S, expPoly (P μ) μ s) ∧
        ∑ μ ∈ S, ((d - 1) * (P μ).natDegree + 1) = N := by sorry
