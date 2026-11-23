-- Prove2me | Theorems.Thm_KernelRank_singleRealCoeff_of_ne_deg
-- name    : KernelRank.singleRealCoeff_of_ne_deg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T02:15:19.434872+00:00
-- url     : https://prove2.me/theorems/72a33dc9-84ec-484c-b07b-e2daeb2998ae
-- title:
--   Kernel Rank: single Real Coeff of ne deg
-- statement:
--   The Kernel Rank construction uses the single Real Coeff of ne deg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiRealRank.lean#L961-L964
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiRealRank.lean#L961-L964

import Definitions.Def_KernelRankLean_MultiComplexRank
import Definitions.Def_KernelRankLean_RealExpPoly
import Definitions.Def_KernelRankLean_MultiRealRank
set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank

theorem KernelRank.singleRealCoeff_of_ne_deg {ι : Type*} [DecidableEq ι] {m : ι → ℕ} (i₀ : ι)
    (q₀ q : Fin (m i₀)) (a : ℝ) (hq : q ≠ q₀) :
    singleRealCoeff i₀ q₀ a i₀ q = 0 := by sorry
