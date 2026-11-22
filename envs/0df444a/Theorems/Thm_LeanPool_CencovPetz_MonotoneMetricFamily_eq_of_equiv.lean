-- Prove2me | Theorems.Thm_LeanPool_CencovPetz_MonotoneMetricFamily_eq_of_equiv
-- name    : LeanPool.CencovPetz.MonotoneMetricFamily.eq_of_equiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:25:56.508546+00:00
-- url     : https://prove2.me/theorems/fd25f5fa-3c99-43f3-83a5-66ce0ad0183d
-- title:
--   Monotone Metric Family: eq of equiv
-- statement:
--   The Monotone Metric Family construction uses the eq of equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/PermutationInvariance.lean#L223-L252
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/PermutationInvariance.lean#L223-L252

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
open LeanPool.CencovPetz.MonotoneMetricFamily

theorem LeanPool.CencovPetz.MonotoneMetricFamily.eq_of_equiv
    (G : MonotoneMetricFamily) (e : α ≃ β) (p : Simplex α)
    (u v : tangentSpace (α := α)) :
    G.g (α := β)
        ((MarkovMorphism.deterministic (α := α) (β := β)
            (g := (e : α → β))
            e.surjective).pushforward p)
        ((MarkovMorphism.deterministic (α := α) (β := β)
            (g := (e : α → β))
            e.surjective).tangentPushforward u)
        ((MarkovMorphism.deterministic (α := α) (β := β)
            (g := (e : α → β))
            e.surjective).tangentPushforward v)
      = G.g (α := α) p u v := by sorry
