-- Prove2me | Theorems.Thm_LeanPool_CencovPetz_MarkovMorphism_deterministic_tangentPushforward_comp_symm
-- name    : LeanPool.CencovPetz.MarkovMorphism.deterministic_tangentPushforward_comp_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:25:59.613564+00:00
-- url     : https://prove2.me/theorems/09063bd7-4fd8-477f-8da6-cc7d7693c066
-- title:
--   Markov Morphism: deterministic tangent Pushforward comp symm
-- statement:
--   The Markov Morphism construction uses the deterministic tangent Pushforward comp symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/PermutationInvariance.lean#L147-L187
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/PermutationInvariance.lean#L147-L187

module
public import Definitions.Def_LeanPool_CencovPetz_SufficientStatistic
public import Definitions.Def_LeanPool_CencovPetz_MonotoneMetric
public import Mathlib.LinearAlgebra.BilinearForm.Hom
public import Definitions.Def_LeanPool_CencovPetz_LeftInverseIsometry
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Definitions.Def_LeanPool_CencovPetz_PermutationInvariance
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.CencovPetz
open scoped BigOperators
universe u
variable {α β : Type u} [Fintype α] [Fintype β]
open LeanPool.CencovPetz.MarkovMorphism

theorem LeanPool.CencovPetz.MarkovMorphism.deterministic_tangentPushforward_comp_symm
    (e : α ≃ β) (u : tangentSpace (α := α)) :
    (MarkovMorphism.deterministic (α := β) (β := α)
        (g := (e.symm : β → α))
        e.symm.surjective).tangentPushforward
      ((MarkovMorphism.deterministic (α := α) (β := β)
          (g := (e : α → β))
          e.surjective).tangentPushforward u)
      = u := by sorry
