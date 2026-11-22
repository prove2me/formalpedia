-- Prove2me | Theorems.Thm_LeanPool_CencovPetz_Simplex_continuous_p
-- name    : LeanPool.CencovPetz.Simplex.continuous_p
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:20:55.829801+00:00
-- url     : https://prove2.me/theorems/15c40ba9-8435-4630-90d7-3ab37224e9d7
-- title:
--   Simplex: continuous p
-- statement:
--   The Simplex construction uses the continuous p property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/SimplexTopology.lean#L43-L44
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/SimplexTopology.lean#L43-L44

module
public import Definitions.Def_LeanPool_CencovPetz_Simplex
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Definitions.Def_LeanPool_CencovPetz_SimplexTopology
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.CencovPetz
open scoped BigOperators
universe u
variable {α : Type u} [Fintype α]
open LeanPool.CencovPetz.Simplex

theorem LeanPool.CencovPetz.Simplex.continuous_p : Continuous fun p : Simplex α => p.p := by sorry
