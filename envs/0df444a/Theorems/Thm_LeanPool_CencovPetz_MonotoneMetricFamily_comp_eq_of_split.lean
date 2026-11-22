-- Prove2me | Theorems.Thm_LeanPool_CencovPetz_MonotoneMetricFamily_comp_eq_of_split
-- name    : LeanPool.CencovPetz.MonotoneMetricFamily.comp_eq_of_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:27:02.205083+00:00
-- url     : https://prove2.me/theorems/e168f95b-7d67-481c-abb5-43a5a77f6d61
-- title:
--   Monotone Metric Family: comp eq of split
-- statement:
--   The Monotone Metric Family construction uses the comp eq of split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/SplittingInvariance.lean#L37-L57
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/SplittingInvariance.lean#L37-L57

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

theorem LeanPool.CencovPetz.MonotoneMetricFamily.comp_eq_of_split (G : MonotoneMetricFamily)
    (m : α → ℕ) (hm : ∀ a, 0 < m a) (p : Simplex α) :
    (G.g (α := MarkovMorphism.SplitTarget (α := α) m)
        ((MarkovMorphism.split (α := α) m hm).pushforward p)).comp
        ((MarkovMorphism.split (α := α) m hm).tangentPushforwardLinear)
        ((MarkovMorphism.split (α := α) m hm).tangentPushforwardLinear)
      = G.g (α := α) p := by sorry
