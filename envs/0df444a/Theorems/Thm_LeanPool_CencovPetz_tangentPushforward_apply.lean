-- Prove2me | Theorems.Thm_LeanPool_CencovPetz_tangentPushforward_apply
-- name    : LeanPool.CencovPetz.tangentPushforward_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:22:26.922034+00:00
-- url     : https://prove2.me/theorems/286e976c-641c-4a96-b053-d2d82f8beea1
-- title:
--   Cencov Petz: tangent Pushforward apply
-- statement:
--   The Cencov Petz construction uses the tangent Pushforward apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/SufficientStatistic.lean#L98-L100
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/SufficientStatistic.lean#L98-L100

module
public import Definitions.Def_LeanPool_CencovPetz_Simplex
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.Order
public import Definitions.Def_LeanPool_CencovPetz_SufficientStatistic
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.CencovPetz
open scoped BigOperators
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]

theorem LeanPool.CencovPetz.tangentPushforward_apply (g : α → β) (u : tangentSpace (α := α)) (b : β) :
    (tangentPushforward (α := α) (β := β) g u : β → ℝ) b = ∑ a with g a = b, ((u : α → ℝ) a) := by sorry

attribute [defeq] LeanPool.CencovPetz.tangentPushforward_apply
