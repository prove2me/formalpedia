-- Prove2me | Theorems.Thm_KernelRank_Component_multiCost_of_isGaussian
-- name    : KernelRank.Component.multiCost_of_isGaussian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:55:03.282356+00:00
-- url     : https://prove2.me/theorems/d50cec23-41f5-44a4-b19b-c159d067178f
-- title:
--   Component: multi Cost of is Gaussian
-- statement:
--   The Component construction uses the multi Cost of is Gaussian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Defs.lean#L160-L163
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Defs.lean#L160-L163

import Mathlib
import Definitions.Def_KernelRankLean_Defs
set_option autoImplicit true
open Complex Polynomial
open KernelRank
open KernelRank.Component

theorem KernelRank.Component.multiCost_of_isGaussian (d : ℕ) {c : Component} (hg : c.IsGaussian) :
    c.multiCost d = c.gaussianCost d := by sorry
