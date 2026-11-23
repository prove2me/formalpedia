-- Prove2me | Theorems.Thm_KernelRank_totalCost_le_of_tendsto_radial_profile
-- name    : KernelRank.totalCost_le_of_tendsto_radial_profile
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T02:22:05.580288+00:00
-- url     : https://prove2.me/theorems/99f74ceb-323b-46d1-8be5-f319452cb694
-- title:
--   Kernel Rank: total Cost le of tendsto radial profile
-- statement:
--   **General `d`-D real border-rank lower bound (`d ≥ 2`).** Every family `F i` converging
--   pointwise along a nontrivial filter to `x ↦ profile cs (∑ j, x j ^ 2)` for a representation `cs`
--   eventually cannot have separable rank strictly below `totalCost cs` (its 2-D rank).
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Approximation.lean#L220-L231
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Approximation.lean#L220-L231

import Definitions.Def_KernelRankLean_Main
import Definitions.Def_KernelRankLean_Approximation
set_option autoImplicit true
open Complex Polynomial
open scoped Topology
open KernelRank

theorem KernelRank.totalCost_le_of_tendsto_radial_profile {d : ℕ} (hd : 2 ≤ d)
    {cs : List Component} (hcs : IsRepresentation cs)
    {ι : Type*} {l : Filter ι} [l.NeBot] {F : ι → (Fin d → ℝ) → ℝ} {r : ℕ}
    (hrank : ∀ᶠ i in l, separableRank (F i) ≤ (r : ℕ))
    (htend : ∀ x, Filter.Tendsto (fun i => F i x) l (𝓝 (profile cs (∑ j, x j ^ 2)))) :
    totalCost cs ≤ r := by sorry
