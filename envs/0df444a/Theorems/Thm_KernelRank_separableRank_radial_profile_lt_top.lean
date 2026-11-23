-- Prove2me | Theorems.Thm_KernelRank_separableRank_radial_profile_lt_top
-- name    : KernelRank.separableRank_radial_profile_lt_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T02:18:46.842607+00:00
-- url     : https://prove2.me/theorems/4099acca-5dc8-4327-a244-b8db54cebb6b
-- title:
--   Kernel Rank: separable Rank radial profile lt top
-- statement:
--   Every list of components gives a `d`-D radial kernel of finite separable rank (`d ≥ 2`).
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiRealRank.lean#L248-L258
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiRealRank.lean#L248-L258

import Definitions.Def_KernelRankLean_MultiComplexRank
import Definitions.Def_KernelRankLean_RealExpPoly
import Definitions.Def_KernelRankLean_MultiRealRank
set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank

theorem KernelRank.separableRank_radial_profile_lt_top {d : ℕ} (hd : 2 ≤ d) (cs : List Component) :
    separableRank (fun x : Fin d → ℝ => profile cs (∑ j, x j ^ 2)) < ⊤ := by sorry
