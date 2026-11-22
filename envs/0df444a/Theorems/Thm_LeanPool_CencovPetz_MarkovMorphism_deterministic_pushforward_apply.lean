-- Prove2me | Theorems.Thm_LeanPool_CencovPetz_MarkovMorphism_deterministic_pushforward_apply
-- name    : LeanPool.CencovPetz.MarkovMorphism.deterministic_pushforward_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:22:23.615388+00:00
-- url     : https://prove2.me/theorems/763161a6-3304-4ce7-85a8-a24d2a88d4ba
-- title:
--   Markov Morphism: deterministic pushforward apply
-- statement:
--   Pushforward along a deterministic morphism is fiberwise summation.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/MarkovMorphism.lean#L167-L177
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/MarkovMorphism.lean#L167-L177

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

theorem LeanPool.CencovPetz.MarkovMorphism.deterministic_pushforward_apply [DecidableEq β] (g : α → β) (hg : Function.Surjective g)
    (p : Simplex α) (b : β) :
    ((deterministic (α := α) (β := β) g hg).pushforward p).p b = ∑ a with g a = b, p.p a := by sorry
