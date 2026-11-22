-- Prove2me | Theorems.Thm_LeanPool_CencovPetz_MarkovMorphism_deterministic_tangentPushforward_apply
-- name    : LeanPool.CencovPetz.MarkovMorphism.deterministic_tangentPushforward_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:22:31.929169+00:00
-- url     : https://prove2.me/theorems/fd5390b5-fba7-4bda-96ff-b2482d6856af
-- title:
--   Markov Morphism: deterministic tangent Pushforward apply
-- statement:
--   Tangent pushforward along a deterministic morphism is fiberwise summation.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/MarkovMorphism.lean#L180-L192
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/MarkovMorphism.lean#L180-L192

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

theorem LeanPool.CencovPetz.MarkovMorphism.deterministic_tangentPushforward_apply [DecidableEq β]
    (g : α → β) (hg : Function.Surjective g)
    (u : tangentSpace (α := α)) (b : β) :
    ((deterministic (α := α) (β := β) g hg).tangentPushforward u : β → ℝ) b =
      ∑ a with g a = b, ((u : α → ℝ) a) := by sorry
