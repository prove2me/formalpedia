-- Prove2me | Theorems.Thm_KernelRank_singleRealCoeff_of_ne_idx
-- name    : KernelRank.singleRealCoeff_of_ne_idx
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T02:15:14.636944+00:00
-- url     : https://prove2.me/theorems/22349c12-418c-472e-8122-9174b8205bb2
-- title:
--   Kernel Rank: single Real Coeff of ne idx
-- statement:
--   The Kernel Rank construction uses the single Real Coeff of ne idx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiRealRank.lean#L956-L959
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiRealRank.lean#L956-L959

import Definitions.Def_KernelRankLean_MultiComplexRank
import Definitions.Def_KernelRankLean_RealExpPoly
import Definitions.Def_KernelRankLean_MultiRealRank
set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank

theorem KernelRank.singleRealCoeff_of_ne_idx {ι : Type*} [DecidableEq ι] {m : ι → ℕ} {i : ι} (i₀ : ι)
    (q₀ : Fin (m i₀)) (a : ℝ) (hi : i ≠ i₀) (q : Fin (m i)) :
    singleRealCoeff i₀ q₀ a i q = 0 := by sorry
