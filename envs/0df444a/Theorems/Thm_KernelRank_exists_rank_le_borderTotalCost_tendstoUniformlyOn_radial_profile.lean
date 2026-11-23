-- Prove2me | Theorems.Thm_KernelRank_exists_rank_le_borderTotalCost_tendstoUniformlyOn_radial_profile
-- name    : KernelRank.exists_rank_le_borderTotalCost_tendstoUniformlyOn_radial_profile
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T02:21:05.200345+00:00
-- url     : https://prove2.me/theorems/e8128e82-3c90-4417-9728-7292a591c898
-- title:
--   Kernel Rank: exists rank le border Total Cost tendsto Uniformly On radial profile
-- statement:
--   **General `d`-D border-rank bound (`d ≥ 2`).** For every list `cs` of well-formed components,
--   there exists an explicit family `F h` of real kernels on `ℝ^d` having `d`-way separable rank at
--   most `borderTotalCost d cs` for every `h ∈ ℝ` and converging uniformly on every compact subset
--   `C ⊆ ℝ^d` to `x ↦ profile cs (∑ j, x j ^ 2)` as `h → 0` (`h ≠ 0`). Combined with
--   `separableRank_radial_profile` and `multiTotalCost_eq_borderTotalCost_add`, every representation
--   in dimension `d ≥ 3` has an exact-minus-border real rank gap of at least
--   `(d - 2) * ∑_{c ∈ cs} deg P_c`.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Main.lean#L444-L451
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Main.lean#L444-L451

import Definitions.Def_KernelRankLean_Necessity
import Definitions.Def_KernelRankLean_MultiComplexRank
import Definitions.Def_KernelRankLean_MultiRealRank
import Definitions.Def_KernelRankLean_Main
set_option autoImplicit true
open Complex Polynomial Filter Topology
open KernelRank

theorem KernelRank.exists_rank_le_borderTotalCost_tendstoUniformlyOn_radial_profile
    {d : ℕ} (hd : 2 ≤ d) (cs : List Component) (hcs : ∀ c ∈ cs, c.WellFormed) :
    ∃ F : ℝ → (Fin d → ℝ) → ℝ,
      (∀ h, separableRank (F h) ≤ (borderTotalCost d cs : ℕ)) ∧
      ∀ C : Set (Fin d → ℝ), IsCompact C →
        TendstoUniformlyOn F (fun x => profile cs (∑ j, x j ^ 2)) (𝓝[≠] (0 : ℝ)) C := by sorry
