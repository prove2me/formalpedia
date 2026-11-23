-- Prove2me | Theorems.Thm_KernelRank_separableRank_fin2_le_of_tendsto
-- name    : KernelRank.separableRank_fin2_le_of_tendsto
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T02:21:39.354792+00:00
-- url     : https://prove2.me/theorems/7465ffc6-bfc9-464a-8938-19ee6fc4d39b
-- title:
--   Kernel Rank: separable Rank fin2 le of tendsto
-- statement:
--   **Pointwise closure of two-variable separable rank.** Over any Hausdorff topological field,
--   if `F i` eventually has two-coordinate separable rank at most `r` and converges pointwise along a
--   nontrivial filter `l` to `K`, then `separableRank K ≤ r`.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Approximation.lean#L140-L181
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Approximation.lean#L140-L181

import Definitions.Def_KernelRankLean_Main
import Definitions.Def_KernelRankLean_Approximation
set_option autoImplicit true
open Complex Polynomial
open scoped Topology
open KernelRank

theorem KernelRank.separableRank_fin2_le_of_tendsto {𝕜 α ι : Type*} [Field 𝕜] [TopologicalSpace 𝕜]
    [IsTopologicalRing 𝕜] [T2Space 𝕜] {l : Filter ι} [l.NeBot]
    {F : ι → (Fin 2 → α) → 𝕜} {K : (Fin 2 → α) → 𝕜} {r : ℕ}
    (hrank : ∀ᶠ i in l, separableRank (F i) ≤ (r : ℕ))
    (htend : ∀ z, Filter.Tendsto (fun i => F i z) l (𝓝 (K z))) :
    separableRank K ≤ (r : ℕ) := by sorry
