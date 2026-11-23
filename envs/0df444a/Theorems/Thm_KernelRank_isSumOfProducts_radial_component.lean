-- Prove2me | Theorems.Thm_KernelRank_isSumOfProducts_radial_component
-- name    : KernelRank.isSumOfProducts_radial_component
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T02:18:37.170101+00:00
-- url     : https://prove2.me/theorems/32f61a89-33f3-4af0-98be-9b8fd81d5bf0
-- title:
--   Kernel Rank: is Sum Of Products radial component
-- statement:
--   Every exponential-polynomial component has finite `d`-way real separable rank (`d ≥ 2`).
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiRealRank.lean#L237-L245
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiRealRank.lean#L237-L245

import Definitions.Def_KernelRankLean_MultiComplexRank
import Definitions.Def_KernelRankLean_RealExpPoly
import Definitions.Def_KernelRankLean_MultiRealRank
set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank

theorem KernelRank.isSumOfProducts_radial_component {d : ℕ} (hd : 2 ≤ d) (c : Component) :
    IsSumOfProducts (fun x : Fin d → ℝ => c.eval (∑ j, x j ^ 2))
      (((d - 1) * c.poly.natDegree + 1) * d) := by sorry
