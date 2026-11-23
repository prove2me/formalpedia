-- Prove2me | Theorems.Thm_KernelRank_isSumOfProducts_expPoly
-- name    : KernelRank.isSumOfProducts_expPoly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T02:09:08.696388+00:00
-- url     : https://prove2.me/theorems/869936f6-55e7-421a-8079-8829577eff9a
-- title:
--   Kernel Rank: is Sum Of Products exp Poly
-- statement:
--   In `d ≥ 2` coordinates, a single exponential polynomial `expPoly P μ (∑ j, s j)` is a sum of
--   `(d - 1) * P.natDegree + 1` coordinatewise products.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiComplexRank.lean#L231-L290
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiComplexRank.lean#L231-L290

import Definitions.Def_KernelRankLean_ComplexRank
import Definitions.Def_KernelRankLean_MultiComplexRank
set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank

theorem KernelRank.isSumOfProducts_expPoly {d : ℕ} (hd : 2 ≤ d) (P : ℂ[X]) (μ : ℂ) :
    IsSumOfProducts (fun s : Fin d → ℝ≥0 => expPoly P μ (∑ j, (s j : ℝ)))
      ((d - 1) * P.natDegree + 1) := by sorry
