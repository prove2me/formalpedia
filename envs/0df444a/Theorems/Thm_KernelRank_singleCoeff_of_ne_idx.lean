-- Prove2me | Theorems.Thm_KernelRank_singleCoeff_of_ne_idx
-- name    : KernelRank.singleCoeff_of_ne_idx
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T02:08:30.549805+00:00
-- url     : https://prove2.me/theorems/79190f17-c48f-45fe-a0a6-435bfbe28f63
-- title:
--   Kernel Rank: single Coeff of ne idx
-- statement:
--   The Kernel Rank construction uses the single Coeff of ne idx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiComplexRank.lean#L345-L348
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiComplexRank.lean#L345-L348

import Definitions.Def_KernelRankLean_ComplexRank
import Definitions.Def_KernelRankLean_MultiComplexRank
set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank

theorem KernelRank.singleCoeff_of_ne_idx {ι : Type*} [DecidableEq ι] {m₀ : ι → ℕ}
    (i₀ : ι) (q₀ : Fin (m₀ i₀)) (z : ℂ) {i : ι} (hi : i ≠ i₀) (q : Fin (m₀ i)) :
    singleCoeff i₀ q₀ z i q = 0 := by sorry
