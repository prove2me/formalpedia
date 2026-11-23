-- Prove2me | Theorems.Thm_KernelRank_borderTotalCost_eq_totalCost_of_forall_im_eq_zero
-- name    : KernelRank.borderTotalCost_eq_totalCost_of_forall_im_eq_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T02:21:47.853919+00:00
-- url     : https://prove2.me/theorems/bddb9022-a520-4121-8cbc-95d0ceb9700b
-- title:
--   Kernel Rank: border Total Cost eq total Cost of forall im eq zero
-- statement:
--   **Sharpness of `borderTotalCost` for all purely real-rate representations (`d ≥ 2`).**
--   When every component of `cs` has a real rate (`c.rate.im = 0`, of arbitrary polynomial degree),
--   `borderTotalCost d cs` coincides with the 2-D rank `totalCost cs`.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Approximation.lean#L236-L242
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Approximation.lean#L236-L242

import Definitions.Def_KernelRankLean_Main
import Definitions.Def_KernelRankLean_Approximation
set_option autoImplicit true
open Complex Polynomial
open scoped Topology
open KernelRank

theorem KernelRank.borderTotalCost_eq_totalCost_of_forall_im_eq_zero (d : ℕ) {cs : List Component}
    (him : ∀ c ∈ cs, c.rate.im = 0) :
    borderTotalCost d cs = totalCost cs := by sorry
