-- Prove2me | Theorems.Thm_KernelRank_separableRank_sum_expPoly
-- name    : KernelRank.separableRank_sum_expPoly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T02:16:12.655038+00:00
-- url     : https://prove2.me/theorems/9186975d-1ec9-4337-9b50-5bfd4a8841b5
-- title:
--   Kernel Rank: separable Rank sum exp Poly
-- statement:
--   **Exact `d`-way complex Hankel rank of exponential polynomials (`d ≥ 2`).**
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiComplexRank.lean#L975-L1005
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiComplexRank.lean#L975-L1005

import Definitions.Def_KernelRankLean_ComplexRank
import Definitions.Def_KernelRankLean_MultiComplexRank
set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank

theorem KernelRank.separableRank_sum_expPoly {d : ℕ} (hd : 2 ≤ d) {ι : Type*} [Fintype ι] {rate : ι → ℂ}
    (hinj : Function.Injective rate) (P : ι → ℂ[X]) (hP : ∀ i, P i ≠ 0) :
    separableRank (fun s : Fin d → ℝ≥0 => ∑ i, expPoly (P i) (rate i) (∑ j, (s j : ℝ))) =
      (∑ i, ((d - 1) * (P i).natDegree + 1) : ℕ) := by sorry
