-- Prove2me | Theorems.Thm_LeanPool_CencovPetz_MarkovMorphism_tangentPushforwardLinear_apply
-- name    : LeanPool.CencovPetz.MarkovMorphism.tangentPushforwardLinear_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:22:21.330483+00:00
-- url     : https://prove2.me/theorems/111bc250-92a8-46b9-88b2-9e9cc4135936
-- title:
--   Markov Morphism: tangent Pushforward Linear apply
-- statement:
--   The Markov Morphism construction uses the tangent Pushforward Linear apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/MarkovMorphism.lean#L162-L164
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/MarkovMorphism.lean#L162-L164

module
public import Definitions.Def_LeanPool_CencovPetz_Simplex
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.Order
public import Definitions.Def_LeanPool_CencovPetz_MarkovMorphism
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.CencovPetz
open scoped BigOperators
variable {α β : Type*} [Fintype α] [Fintype β]
open LeanPool.CencovPetz.MarkovMorphism
variable (κ : MarkovMorphism α β)

theorem LeanPool.CencovPetz.MarkovMorphism.tangentPushforwardLinear_apply (u : tangentSpace (α := α)) :
    κ.tangentPushforwardLinear u = κ.tangentPushforward u := by sorry

attribute [defeq] LeanPool.CencovPetz.MarkovMorphism.tangentPushforwardLinear_apply
