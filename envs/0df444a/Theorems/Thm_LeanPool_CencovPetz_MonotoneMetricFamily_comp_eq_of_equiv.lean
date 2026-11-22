-- Prove2me | Theorems.Thm_LeanPool_CencovPetz_MonotoneMetricFamily_comp_eq_of_equiv
-- name    : LeanPool.CencovPetz.MonotoneMetricFamily.comp_eq_of_equiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:26:08.334848+00:00
-- url     : https://prove2.me/theorems/0afa1175-c236-4074-ad2e-157c0efb0786
-- title:
--   Monotone Metric Family: comp eq of equiv
-- statement:
--   The Monotone Metric Family construction uses the comp eq of equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/PermutationInvariance.lean#L193-L221
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/PermutationInvariance.lean#L193-L221

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

theorem LeanPool.CencovPetz.MonotoneMetricFamily.comp_eq_of_equiv
    (G : MonotoneMetricFamily) (e : α ≃ β) (p : Simplex α) :
    (G.g (α := β)
        ((MarkovMorphism.deterministic (α := α) (β := β)
            (g := (e : α → β))
            e.surjective).pushforward p)).comp
        ((MarkovMorphism.deterministic (α := α) (β := β)
            (g := (e : α → β))
            e.surjective).tangentPushforwardLinear)
        ((MarkovMorphism.deterministic (α := α) (β := β)
            (g := (e : α → β))
            e.surjective).tangentPushforwardLinear)
      = G.g (α := α) p := by sorry
