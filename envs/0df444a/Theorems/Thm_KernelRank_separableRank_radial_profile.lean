-- Prove2me | Theorems.Thm_KernelRank_separableRank_radial_profile
-- name    : KernelRank.separableRank_radial_profile
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T02:14:52.253591+00:00
-- url     : https://prove2.me/theorems/a4fc6d85-2c3f-470c-9feb-498b4b63bf90
-- title:
--   Kernel Rank: separable Rank radial profile
-- statement:
--   **Exact `d`-way real radial rank of any representation (`d ≥ 2`).**
--   Each real-rate component contributes `(d - 1) * deg P + 1` real `d`-way products, and each
--   nonreal conjugate-pair component contributes `2 * (d - 1) * deg P + d`.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiRealRank.lean#L2418-L2547
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiRealRank.lean#L2418-L2547

import Definitions.Def_KernelRankLean_MultiComplexRank
import Definitions.Def_KernelRankLean_RealExpPoly
import Definitions.Def_KernelRankLean_MultiRealRank
set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank
open scoped Classical

theorem KernelRank.separableRank_radial_profile {d : ℕ} (hd : 2 ≤ d) {cs : List Component}
    (hcs : IsRepresentation cs) :
    separableRank (fun x : Fin d → ℝ => profile cs (∑ j, x j ^ 2)) =
      multiTotalCost d cs := by sorry
