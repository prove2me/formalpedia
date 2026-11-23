-- Prove2me | Theorems.Thm_KernelRank_multiTotalCost_of_isGaussian
-- name    : KernelRank.multiTotalCost_of_isGaussian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:55:25.995916+00:00
-- url     : https://prove2.me/theorems/ed087bc5-94da-4edf-ba84-3740db0b5cc9
-- title:
--   Kernel Rank: multi Total Cost of is Gaussian
-- statement:
--   The Kernel Rank construction uses the multi Total Cost of is Gaussian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Defs.lean#L223-L228
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Defs.lean#L223-L228

import Mathlib
import Definitions.Def_KernelRankLean_Defs
set_option autoImplicit true
open Complex Polynomial
open KernelRank

theorem KernelRank.multiTotalCost_of_isGaussian {d : ℕ} {cs : List Component}
    (hg : ∀ c ∈ cs, c.IsGaussian) :
    multiTotalCost d cs = gaussianTotalCost d cs := by sorry
