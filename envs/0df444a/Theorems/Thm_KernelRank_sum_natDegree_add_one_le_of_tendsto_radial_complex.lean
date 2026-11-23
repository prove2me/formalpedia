-- Prove2me | Theorems.Thm_KernelRank_sum_natDegree_add_one_le_of_tendsto_radial_complex
-- name    : KernelRank.sum_natDegree_add_one_le_of_tendsto_radial_complex
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T02:43:35.715809+00:00
-- url     : https://prove2.me/theorems/30b56f9c-4b23-4151-a1f9-1a900161e520
-- title:
--   Kernel Rank: sum nat Degree add one le of tendsto radial complex
-- statement:
--   **Exact `d`-D complex border-rank lower bound (`d ≥ 2`).** Every family `F i` of complex
--   kernels on `ℝ^d` converging pointwise along a nontrivial filter to
--   `x ↦ ∑ μ ∈ S, expPoly (P μ) μ (∑ j, x j ^ 2)` (with `P μ ≠ 0` for `μ ∈ S`) eventually cannot have
--   separable rank strictly below `∑ μ ∈ S, ((P μ).natDegree + 1)`.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Approximation.lean#L262-L286
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Approximation.lean#L262-L286

import Definitions.Def_KernelRankLean_Main
import Definitions.Def_KernelRankLean_Approximation
set_option autoImplicit true
open Complex Polynomial
open scoped Topology
open KernelRank

theorem KernelRank.sum_natDegree_add_one_le_of_tendsto_radial_complex {d : ℕ} (hd : 2 ≤ d)
    {S : Finset ℂ} {P : ℂ → ℂ[X]} (hP : ∀ μ ∈ S, P μ ≠ 0)
    {ι : Type*} {l : Filter ι} [l.NeBot] {F : ι → (Fin d → ℝ) → ℂ} {r : ℕ}
    (hrank : ∀ᶠ i in l, separableRank (F i) ≤ (r : ℕ))
    (htend : ∀ x, Filter.Tendsto (fun i => F i x) l
      (𝓝 (∑ μ ∈ S, expPoly (P μ) μ (∑ j, x j ^ 2)))) :
    (∑ μ ∈ S, ((P μ).natDegree + 1)) ≤ r := by sorry
