-- Prove2me | Theorems.Thm_KernelRank_exists_rank_le_sum_natDegree_add_one_tendstoUniformlyOn_radial_complex
-- name    : KernelRank.exists_rank_le_sum_natDegree_add_one_tendstoUniformlyOn_radial_complex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T02:44:39.982712+00:00
-- url     : https://prove2.me/theorems/25cdb854-6f93-4f19-a839-97d1b93f5abc
-- title:
--   Kernel Rank: exists rank le sum nat Degree add one tendsto Uniformly On radial complex
-- statement:
--   **Exact `d`-D complex border-rank upper bound (`d ≥ 2`).** For every finite set of rates `S`
--   and polynomials `P : ℂ → ℂ[X]`, there exists an explicit family `F h` of complex kernels on `ℝ^d`
--   having `d`-way separable rank at most `∑ μ ∈ S, ((P μ).natDegree + 1)` for every `h ∈ ℝ` and
--   converging uniformly on every compact subset `C ⊆ ℝ^d` to
--   `x ↦ ∑ μ ∈ S, expPoly (P μ) μ (∑ j, x j ^ 2)` as `h → 0` (`h ≠ 0`). Together with
--   `sum_natDegree_add_one_le_of_tendsto_radial_complex`, the pointwise and compact-open complex border
--   rank of any radial exponential polynomial equals `∑ μ ∈ S, ((P μ).natDegree + 1)` (when `P μ ≠ 0`
--   on `S`).
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Approximation.lean#L296-L445
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Approximation.lean#L296-L445

import Definitions.Def_KernelRankLean_Main
import Definitions.Def_KernelRankLean_Approximation
set_option autoImplicit true
open Complex Polynomial
open scoped Topology
open KernelRank

theorem KernelRank.exists_rank_le_sum_natDegree_add_one_tendstoUniformlyOn_radial_complex
    {d : ℕ} (hd : 2 ≤ d) (S : Finset ℂ) (P : ℂ → ℂ[X]) :
    ∃ F : ℝ → (Fin d → ℝ) → ℂ,
      (∀ h, separableRank (F h) ≤ (∑ μ ∈ S, ((P μ).natDegree + 1) : ℕ)) ∧
      ∀ C : Set (Fin d → ℝ), IsCompact C →
        TendstoUniformlyOn F (fun x => ∑ μ ∈ S, expPoly (P μ) μ (∑ j, x j ^ 2))
          (𝓝[≠] (0 : ℝ)) C := by sorry
