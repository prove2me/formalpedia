-- Prove2me | Theorems.Thm_KernelRank_exists_rank_le_five_tendstoUniformlyOn_radial_sq_mul_cos
-- name    : KernelRank.exists_rank_le_five_tendstoUniformlyOn_radial_sq_mul_cos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T02:44:55.370214+00:00
-- url     : https://prove2.me/theorems/ee8ce96e-f473-42df-a0b0-f2ffc9dec534
-- title:
--   Kernel Rank: exists rank le five tendsto Uniformly On radial sq mul cos
-- statement:
--   **Non-Gaussian border-rank upper bound `≤ 5 < B_3 = 6` for `‖x‖² cos(‖x‖²)` on `ℝ³`.**
--   There exists an explicit family `F h` of real separable kernels of rank at most `5` on `ℝ³`
--   converging uniformly on every compact subset `C ⊆ ℝ³` to `‖x‖² cos(‖x‖²)` as `h → 0` (`h ≠ 0`).
--   Together with `not_exists_rank_le_four_tendsto_radial_sq_mul_cos`, the exact pointwise and
--   compact-open real border rank of `‖x‖² cos(‖x‖²)` on `ℝ³` is `5`, strictly below both its exact
--   real rank `C_3 = 7` and the radial multi-Gaussian border-rank bound `B_3 = 6`.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Approximation.lean#L737-L823
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Approximation.lean#L737-L823

import Definitions.Def_KernelRankLean_Main
import Definitions.Def_KernelRankLean_Approximation
set_option autoImplicit true
open Complex Polynomial
open scoped Topology
open KernelRank

theorem KernelRank.exists_rank_le_five_tendstoUniformlyOn_radial_sq_mul_cos :
    ∃ F : ℝ → (Fin 3 → ℝ) → ℝ,
      (∀ h, separableRank (F h) ≤ (5 : ℕ)) ∧
      ∀ C : Set (Fin 3 → ℝ), IsCompact C →
        TendstoUniformlyOn F (fun x => (∑ j, x j ^ 2) * Real.cos (∑ j, x j ^ 2))
          (𝓝[≠] (0 : ℝ)) C := by sorry
