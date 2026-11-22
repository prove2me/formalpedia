-- Prove2me | Theorems.Thm_LeanPool_CencovPetz_MonotoneMetricFamily_eq_of_split
-- name    : LeanPool.CencovPetz.MonotoneMetricFamily.eq_of_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:26:10.739926+00:00
-- url     : https://prove2.me/theorems/c2526b70-82a2-4ef1-ac70-46bf8a4102fe
-- title:
--   Monotone Metric Family: eq of split
-- statement:
--   The Monotone Metric Family construction uses the eq of split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/SplittingInvariance.lean#L59-L80
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/SplittingInvariance.lean#L59-L80

module
public import Definitions.Def_LeanPool_CencovPetz_Splitting
public import Definitions.Def_LeanPool_CencovPetz_MonotoneMetric
public import Mathlib.LinearAlgebra.BilinearForm.Hom
public import Definitions.Def_LeanPool_CencovPetz_LeftInverseIsometry
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Definitions.Def_LeanPool_CencovPetz_SplittingInvariance
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.CencovPetz
open scoped BigOperators
universe u
variable {α : Type u} [Fintype α]
open LeanPool.CencovPetz.MonotoneMetricFamily

theorem LeanPool.CencovPetz.MonotoneMetricFamily.eq_of_split (G : MonotoneMetricFamily)
    (m : α → ℕ) (hm : ∀ a, 0 < m a) (p : Simplex α)
    (u v : tangentSpace (α := α)) :
    G.g (α := MarkovMorphism.SplitTarget (α := α) m)
        ((MarkovMorphism.split (α := α) m hm).pushforward p)
        ((MarkovMorphism.split (α := α) m hm).tangentPushforward u)
        ((MarkovMorphism.split (α := α) m hm).tangentPushforward v)
      = G.g (α := α) p u v := by sorry
