-- Prove2me | Theorems.Thm_LeanPool_CencovPetz_MonotoneMetricFamily_eq_smul_fisher_of_continuous
-- name    : LeanPool.CencovPetz.MonotoneMetricFamily.eq_smul_fisher_of_continuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:29:37.489994+00:00
-- url     : https://prove2.me/theorems/3941de5e-223b-4ae5-9df9-5bba6693f4c1
-- title:
--   Monotone Metric Family: eq smul fisher of continuous
-- statement:
--   The Monotone Metric Family construction uses the eq smul fisher of continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/CencovFinite.lean#L46-L69
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/CencovFinite.lean#L46-L69

module
public import Definitions.Def_LeanPool_CencovPetz_SimplexTopology
public import Definitions.Def_LeanPool_CencovPetz_UniformScalarConstant
public import Definitions.Def_LeanPool_CencovPetz_CencovSplitPoint
public import Definitions.Def_LeanPool_CencovPetz_ContinuousExtension
public import Definitions.Def_LeanPool_CencovPetz_FisherContinuity
public import Definitions.Def_LeanPool_CencovPetz_RationalDensity
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Data.EReal.Inv
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Definitions.Def_LeanPool_CencovPetz_CencovFinite
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.CencovPetz
open scoped BigOperators
open LeanPool.CencovPetz.MonotoneMetricFamily

theorem LeanPool.CencovPetz.MonotoneMetricFamily.eq_smul_fisher_of_continuous (G : MonotoneMetricFamily)
    {α : Type} [Fintype α] [Nonempty α]
    {a0 a1 : α} (ha01 : a0 ≠ a1)
    (hG : ∀ u v : tangentSpace (α := α), Continuous fun p : Simplex α => G.g (α := α) p u v) :
    ∀ (p : Simplex α) (u v : tangentSpace (α := α)),
      G.g (α := α) p u v = (uniformScalar G 2 (by decide)) * fisherBilin p u v := by sorry
