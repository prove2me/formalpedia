-- Prove2me | Theorems.Thm_KernelRank_separableRank_radial_two_profile
-- name    : KernelRank.separableRank_radial_two_profile
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T02:21:06.46551+00:00
-- url     : https://prove2.me/theorems/26550822-873e-490f-85bf-0c943daf0060
-- title:
--   Kernel Rank: separable Rank radial two profile
-- statement:
--   **2-D Sufficiency.** The profile of a representation gives a 2-D radial kernel whose
--   separable rank is `totalCost cs`.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiRealRank.lean#L2558-L2560
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiRealRank.lean#L2558-L2560

import Definitions.Def_KernelRankLean_MultiComplexRank
import Definitions.Def_KernelRankLean_RealExpPoly
import Definitions.Def_KernelRankLean_MultiRealRank
set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank

theorem KernelRank.separableRank_radial_two_profile {cs : List Component} (hcs : IsRepresentation cs) :
    separableRank (fun x : Fin 2 → ℝ => profile cs (∑ j, x j ^ 2)) = totalCost cs := by sorry
