-- Prove2me | Theorems.Thm_KernelRank_iteratedDerivWithin_sum_expPoly
-- name    : KernelRank.iteratedDerivWithin_sum_expPoly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T02:11:02.498806+00:00
-- url     : https://prove2.me/theorems/aa72ae1a-4bec-4c7f-a352-670f1cf09295
-- title:
--   Kernel Rank: iterated Deriv Within sum exp Poly
-- statement:
--   The Kernel Rank construction uses the iterated Deriv Within sum exp Poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/ComplexRank.lean#L116-L134
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/ComplexRank.lean#L116-L134

import Definitions.Def_KernelRankLean_Differential
import Definitions.Def_KernelRankLean_RealExpPoly
import Definitions.Def_KernelRankLean_ComplexRank
set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank

theorem KernelRank.iteratedDerivWithin_sum_expPoly {ι : Type*} [Fintype ι]
    (P : ι → ℂ[X]) (rate : ι → ℂ) (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    iteratedDerivWithin k (fun u => ∑ i, expPoly (P i) (rate i) u) (Set.Ici 0) t =
      ∑ i, expPoly ((((derivative : Module.End ℂ ℂ[X]) + rate i • 1) ^ k) (P i)) (rate i) t := by sorry
