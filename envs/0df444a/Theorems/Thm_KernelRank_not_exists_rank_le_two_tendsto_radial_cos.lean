-- Prove2me | Theorems.Thm_KernelRank_not_exists_rank_le_two_tendsto_radial_cos
-- name    : KernelRank.not_exists_rank_le_two_tendsto_radial_cos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T02:45:21.041039+00:00
-- url     : https://prove2.me/theorems/ed20c815-12b4-495e-a6fc-85be99f23e75
-- title:
--   Kernel Rank: not exists rank le two tendsto radial cos
-- statement:
--   **Sharpness of `B_3 = 3` for a pure nonreal Gaussian on `ℝ³`.** No family of real kernels of
--   separable rank at most `2` converges even pointwise along a nontrivial filter to `cos(‖x‖²)` on
--   `ℝ³`. Since `separableRank (x ↦ cos(‖x‖²)) = 3`, its pointwise and compact-open real border rank
--   is `3`.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Approximation.lean#L577-L601
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Approximation.lean#L577-L601

import Definitions.Def_KernelRankLean_Main
import Definitions.Def_KernelRankLean_Approximation
set_option autoImplicit true
open Complex Polynomial
open scoped Topology
open KernelRank

theorem KernelRank.not_exists_rank_le_two_tendsto_radial_cos {ι : Type*} {l : Filter ι} [l.NeBot]
    {F : ι → (Fin 3 → ℝ) → ℝ}
    (hrank : ∀ᶠ i in l, separableRank (F i) ≤ (2 : ℕ))
    (htend : ∀ x, Filter.Tendsto (fun i => F i x) l (𝓝 (Real.cos (∑ j, x j ^ 2)))) : False := by sorry
