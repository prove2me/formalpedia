-- Prove2me | Theorems.Thm_KernelRank_abs_exp_sub_one_sub_le
-- name    : KernelRank.abs_exp_sub_one_sub_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T02:16:29.270801+00:00
-- url     : https://prove2.me/theorems/bce8703a-b962-4eab-a68a-7cd5131cd5ae
-- title:
--   Kernel Rank: abs exp sub one sub le
-- statement:
--   The Kernel Rank construction uses the abs exp sub one sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Main.lean#L163-L195
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Main.lean#L163-L195

import Definitions.Def_KernelRankLean_Necessity
import Definitions.Def_KernelRankLean_MultiComplexRank
import Definitions.Def_KernelRankLean_MultiRealRank
import Definitions.Def_KernelRankLean_Main
set_option autoImplicit true
open Complex Polynomial Filter Topology
open KernelRank

theorem KernelRank.abs_exp_sub_one_sub_le (y : ℝ) :
    |Real.exp y - 1 - y| ≤ y ^ 2 * Real.exp |y| := by sorry
