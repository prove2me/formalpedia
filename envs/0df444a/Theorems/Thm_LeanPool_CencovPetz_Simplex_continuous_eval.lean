-- Prove2me | Theorems.Thm_LeanPool_CencovPetz_Simplex_continuous_eval
-- name    : LeanPool.CencovPetz.Simplex.continuous_eval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:20:58.784449+00:00
-- url     : https://prove2.me/theorems/4bcaf374-3526-404d-92f1-2e4e5d2e6b9a
-- title:
--   Simplex: continuous eval
-- statement:
--   The Simplex construction uses the continuous eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/SimplexTopology.lean#L46-L47
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/SimplexTopology.lean#L46-L47

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

theorem LeanPool.CencovPetz.Simplex.continuous_eval (a : α) : Continuous fun p : Simplex α => p.p a := by sorry
