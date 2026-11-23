-- Prove2me | Theorems.Thm_KernelRank_singleCoeff_of_ne_deg
-- name    : KernelRank.singleCoeff_of_ne_deg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T02:08:22.846258+00:00
-- url     : https://prove2.me/theorems/bbdde121-9348-4611-ad76-085a6e5d875f
-- title:
--   Kernel Rank: single Coeff of ne deg
-- statement:
--   The Kernel Rank construction uses the single Coeff of ne deg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiComplexRank.lean#L350-L353
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiComplexRank.lean#L350-L353

import Definitions.Def_KernelRankLean_ComplexRank
import Definitions.Def_KernelRankLean_MultiComplexRank
set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank

theorem KernelRank.singleCoeff_of_ne_deg {ι : Type*} [DecidableEq ι] {m₀ : ι → ℕ}
    (i₀ : ι) (q₀ q : Fin (m₀ i₀)) (z : ℂ) (hq : q ≠ q₀) :
    singleCoeff i₀ q₀ z i₀ q = 0 := by sorry
