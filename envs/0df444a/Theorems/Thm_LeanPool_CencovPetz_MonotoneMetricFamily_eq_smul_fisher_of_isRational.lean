-- Prove2me | Theorems.Thm_LeanPool_CencovPetz_MonotoneMetricFamily_eq_smul_fisher_of_isRational
-- name    : LeanPool.CencovPetz.MonotoneMetricFamily.eq_smul_fisher_of_isRational
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:29:22.774354+00:00
-- url     : https://prove2.me/theorems/6fff00a8-d86c-463e-9f8f-c6539b9508b8
-- title:
--   Monotone Metric Family: eq smul fisher of is Rational
-- statement:
--   The Monotone Metric Family construction uses the eq smul fisher of is Rational property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/CencovSplitPoint.lean#L225-L232
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/CencovSplitPoint.lean#L225-L232

module
public import Definitions.Def_LeanPool_CencovPetz_RationalPoint
public import Definitions.Def_LeanPool_CencovPetz_UniformScalarConstant
public import Definitions.Def_LeanPool_CencovPetz_PermutationInvariance
public import Definitions.Def_LeanPool_CencovPetz_SplittingInvariance
public import Definitions.Def_LeanPool_CencovPetz_UniformScalarMultiple
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Definitions.Def_LeanPool_CencovPetz_CencovSplitPoint
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.CencovPetz
open scoped BigOperators
open LeanPool.CencovPetz.MonotoneMetricFamily
open MarkovMorphism

theorem LeanPool.CencovPetz.MonotoneMetricFamily.eq_smul_fisher_of_isRational (G : MonotoneMetricFamily)
    {α : Type} [Fintype α] [Nonempty α]
    (p : Simplex α) (hp : Simplex.IsRational (α := α) p)
    {a0 a1 : α} (ha01 : a0 ≠ a1) :
    ∀ u v : tangentSpace (α := α),
      G.g (α := α) p u v = (uniformScalar G 2 (by decide)) * fisherBilin p u v := by sorry
