-- Prove2me | Theorems.Thm_KernelRank_isSumOfProducts_radial_multiComponent
-- name    : KernelRank.isSumOfProducts_radial_multiComponent
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T02:18:38.12641+00:00
-- url     : https://prove2.me/theorems/653fa08b-aa35-402d-888c-bacf48690171
-- title:
--   Kernel Rank: is Sum Of Products radial multi Component
-- statement:
--   Every well-formed component `c` has `d`-way real radial separable rank at most
--   `c.multiCost d` (`d ≥ 2`).
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiRealRank.lean#L664-L843
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiRealRank.lean#L664-L843

import Definitions.Def_KernelRankLean_MultiComplexRank
import Definitions.Def_KernelRankLean_RealExpPoly
import Definitions.Def_KernelRankLean_MultiRealRank
set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank

theorem KernelRank.isSumOfProducts_radial_multiComponent {d : ℕ} (hd : 2 ≤ d) {c : Component}
    (hwf : c.WellFormed) :
    IsSumOfProducts (fun x : Fin d → ℝ => c.eval (∑ j, x j ^ 2)) (c.multiCost d) := by sorry
