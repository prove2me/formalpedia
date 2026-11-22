-- Prove2me | Theorems.Thm_LeanPool_CencovPetz_Simplex_continuous_fisherBilin_apply
-- name    : LeanPool.CencovPetz.Simplex.continuous_fisherBilin_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:21:12.077458+00:00
-- url     : https://prove2.me/theorems/6a371680-c165-45cd-8a7f-134507e3463f
-- title:
--   Simplex: continuous fisher Bilin apply
-- statement:
--   The Simplex construction uses the continuous fisher Bilin apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/FisherContinuity.lean#L38-L61
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/FisherContinuity.lean#L38-L61

module
public import Definitions.Def_LeanPool_CencovPetz_SimplexTopology
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Definitions.Def_LeanPool_CencovPetz_FisherContinuity
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.CencovPetz
open scoped BigOperators
open LeanPool.CencovPetz.Simplex
variable {α : Type*} [Fintype α]

theorem LeanPool.CencovPetz.Simplex.continuous_fisherBilin_apply (u v : tangentSpace (α := α)) :
    Continuous fun p : Simplex α => fisherBilin p u v := by sorry
