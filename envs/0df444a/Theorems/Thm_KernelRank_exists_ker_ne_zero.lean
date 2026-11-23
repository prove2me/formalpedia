-- Prove2me | Theorems.Thm_KernelRank_exists_ker_ne_zero
-- name    : KernelRank.exists_ker_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T02:16:21.455181+00:00
-- url     : https://prove2.me/theorems/504e5ca4-4bbc-468d-b197-f58668d309ba
-- title:
--   Kernel Rank: exists ker ne zero
-- statement:
--   Every `ℝ`-linear functional `ℂ →ₗ[ℝ] ℝ` has a nonzero vector in its kernel.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiRealRank.lean#L849-L860
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiRealRank.lean#L849-L860

import Definitions.Def_KernelRankLean_MultiComplexRank
import Definitions.Def_KernelRankLean_RealExpPoly
import Definitions.Def_KernelRankLean_MultiRealRank
set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank

theorem KernelRank.exists_ker_ne_zero (L : ℂ →ₗ[ℝ] ℝ) : ∃ w : ℂ, w ≠ 0 ∧ L w = 0 := by sorry
