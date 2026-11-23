-- Prove2me | Theorems.Thm_KernelRank_singleCoeff_same
-- name    : KernelRank.singleCoeff_same
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T02:08:17.945918+00:00
-- url     : https://prove2.me/theorems/34bcfe9e-f2fa-4f60-a7f5-85bad8f52140
-- title:
--   Kernel Rank: single Coeff same
-- statement:
--   The Kernel Rank construction uses the single Coeff same property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiComplexRank.lean#L340-L343
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiComplexRank.lean#L340-L343

import Definitions.Def_KernelRankLean_ComplexRank
import Definitions.Def_KernelRankLean_MultiComplexRank
set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank

theorem KernelRank.singleCoeff_same {ι : Type*} [DecidableEq ι] {m₀ : ι → ℕ}
    (i₀ : ι) (q₀ : Fin (m₀ i₀)) (z : ℂ) :
    singleCoeff i₀ q₀ z i₀ q₀ = z := by sorry
