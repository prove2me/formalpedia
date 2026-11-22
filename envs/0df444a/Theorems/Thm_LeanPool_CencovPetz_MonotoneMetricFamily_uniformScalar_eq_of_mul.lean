-- Prove2me | Theorems.Thm_LeanPool_CencovPetz_MonotoneMetricFamily_uniformScalar_eq_of_mul
-- name    : LeanPool.CencovPetz.MonotoneMetricFamily.uniformScalar_eq_of_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:28:45.971852+00:00
-- url     : https://prove2.me/theorems/8f3afb77-12bd-4242-898d-1d936a955c3c
-- title:
--   Monotone Metric Family: uniform Scalar eq of mul
-- statement:
--   The Monotone Metric Family construction uses the uniform Scalar eq of mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/UniformScalarConstant.lean#L64-L218
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/UniformScalarConstant.lean#L64-L218

module
public import Definitions.Def_LeanPool_CencovPetz_PermutationInvariantBilinForm
public import Definitions.Def_LeanPool_CencovPetz_PermutationInvariance
public import Definitions.Def_LeanPool_CencovPetz_ReplicationInvariance
public import Definitions.Def_LeanPool_CencovPetz_UniformScalarMultiple
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Definitions.Def_LeanPool_CencovPetz_UniformScalarConstant
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.CencovPetz
open scoped BigOperators
open LeanPool.CencovPetz.MonotoneMetricFamily
open MarkovMorphism TangentFin

theorem LeanPool.CencovPetz.MonotoneMetricFamily.uniformScalar_eq_of_mul (G : MonotoneMetricFamily) {n m : ℕ} (hn : 2 ≤ n) (hm : 0 < m) :
    uniformScalar G (Fintype.card (Fin n × Fin m))
      (by exact two_le_card_prod (n := n) (m := m) hn hm)
      =
      uniformScalar G n hn := by sorry
