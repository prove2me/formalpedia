-- Prove2me | Theorems.Thm_KernelRank_not_exists_rank_le_four_tendsto_radial_sq_mul_cos
-- name    : KernelRank.not_exists_rank_le_four_tendsto_radial_sq_mul_cos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T02:44:51.186025+00:00
-- url     : https://prove2.me/theorems/bd31d181-af69-4d87-ae21-3582fa02fef5
-- title:
--   Kernel Rank: not exists rank le four tendsto radial sq mul cos
-- statement:
--   **Pointwise real border-rank lower bound `≥ 5` for `‖x‖² cos(‖x‖²)` on `ℝ³`.**
--   No family of real kernels on `ℝ³` of separable rank at most `4` can converge pointwise along a
--   nontrivial filter to `‖x‖² cos(‖x‖²)`.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Approximation.lean#L606-L729
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Approximation.lean#L606-L729

import Definitions.Def_KernelRankLean_Main
import Definitions.Def_KernelRankLean_Approximation
set_option autoImplicit true
open Complex Polynomial
open scoped Topology
open KernelRank

theorem KernelRank.not_exists_rank_le_four_tendsto_radial_sq_mul_cos {ι : Type*} {l : Filter ι} [l.NeBot]
    {F : ι → (Fin 3 → ℝ) → ℝ}
    (hrank : ∀ᶠ i in l, separableRank (F i) ≤ (4 : ℕ))
    (htend : ∀ x, Filter.Tendsto (fun i => F i x) l
      (𝓝 ((∑ j, x j ^ 2) * Real.cos (∑ j, x j ^ 2)))) : False := by sorry
