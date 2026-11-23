-- Prove2me | Theorems.Thm_KernelRank_separableRank_radial_gaussian_profile
-- name    : KernelRank.separableRank_radial_gaussian_profile
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T02:21:28.836273+00:00
-- url     : https://prove2.me/theorems/730fa839-aa23-47b7-a299-eb3df5f8e580
-- title:
--   Kernel Rank: separable Rank radial gaussian profile
-- statement:
--   **Exact `d`-way real radial rank of a multi-Gaussian representation (`d ≥ 2`).**
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiRealRank.lean#L2550-L2554
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiRealRank.lean#L2550-L2554

import Definitions.Def_KernelRankLean_MultiComplexRank
import Definitions.Def_KernelRankLean_RealExpPoly
import Definitions.Def_KernelRankLean_MultiRealRank
set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank

theorem KernelRank.separableRank_radial_gaussian_profile {d : ℕ} (hd : 2 ≤ d) {cs : List Component}
    (hcs : IsGaussianRepresentation cs) :
    separableRank (fun x : Fin d → ℝ => profile cs (∑ j, x j ^ 2)) =
      gaussianTotalCost d cs := by sorry
