-- Prove2me | Theorems.Thm_KernelRank_borderTotalCost_le_of_tendsto_radial_real_profile
-- name    : KernelRank.borderTotalCost_le_of_tendsto_radial_real_profile
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T02:43:28.282811+00:00
-- url     : https://prove2.me/theorems/e9452d4c-52e3-4cf7-a8df-59a628730dcc
-- title:
--   Kernel Rank: border Total Cost le of tendsto radial real profile
-- statement:
--   **Exact `d`-D real border-rank lower bound for purely real-rate representations (`d ≥ 2`).**
--   Combined with `exists_rank_le_borderTotalCost_tendstoUniformlyOn_radial_profile`, for every
--   representation `cs` whose rates are all real (arbitrary polynomial degrees `deg P ≥ 0`), its
--   pointwise and compact-open real border rank in dimension `d ≥ 2` equals `borderTotalCost d cs`
--   (`= ∑_c (deg P_c + 1)`).
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Approximation.lean#L249-L256
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Approximation.lean#L249-L256

import Definitions.Def_KernelRankLean_Main
import Definitions.Def_KernelRankLean_Approximation
set_option autoImplicit true
open Complex Polynomial
open scoped Topology
open KernelRank

theorem KernelRank.borderTotalCost_le_of_tendsto_radial_real_profile {d : ℕ} (hd : 2 ≤ d)
    {cs : List Component} (hcs : IsRepresentation cs) (him : ∀ c ∈ cs, c.rate.im = 0)
    {ι : Type*} {l : Filter ι} [l.NeBot] {F : ι → (Fin d → ℝ) → ℝ} {r : ℕ}
    (hrank : ∀ᶠ i in l, separableRank (F i) ≤ (r : ℕ))
    (htend : ∀ x, Filter.Tendsto (fun i => F i x) l (𝓝 (profile cs (∑ j, x j ^ 2)))) :
    borderTotalCost d cs ≤ r := by sorry
