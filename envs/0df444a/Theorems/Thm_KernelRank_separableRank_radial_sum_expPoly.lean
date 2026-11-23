-- Prove2me | Theorems.Thm_KernelRank_separableRank_radial_sum_expPoly
-- name    : KernelRank.separableRank_radial_sum_expPoly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T02:17:47.922819+00:00
-- url     : https://prove2.me/theorems/8c8136d7-8b31-4656-8054-514f73d2f7aa
-- title:
--   Kernel Rank: separable Rank radial sum exp Poly
-- statement:
--   **Exact `d`-way complex radial rank of exponential polynomials (`d ≥ 2`).**
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiComplexRank.lean#L1008-L1013
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiComplexRank.lean#L1008-L1013

import Definitions.Def_KernelRankLean_ComplexRank
import Definitions.Def_KernelRankLean_MultiComplexRank
set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank

theorem KernelRank.separableRank_radial_sum_expPoly {d : ℕ} (hd : 2 ≤ d) {ι : Type*} [Fintype ι]
    {rate : ι → ℂ} (hinj : Function.Injective rate) (P : ι → ℂ[X]) (hP : ∀ i, P i ≠ 0) :
    separableRank (fun x : Fin d → ℝ => ∑ i, expPoly (P i) (rate i) (∑ j, x j ^ 2)) =
      (∑ i, ((d - 1) * (P i).natDegree + 1) : ℕ) := by sorry
