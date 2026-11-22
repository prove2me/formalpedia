-- Prove2me | Theorems.Thm_LeanPool_CencovPetz_MonotoneMetricFamily_uniformScalar_eq_uniformScalar_two
-- name    : LeanPool.CencovPetz.MonotoneMetricFamily.uniformScalar_eq_uniformScalar_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:28:46.9267+00:00
-- url     : https://prove2.me/theorems/bd9aed60-7eb7-4f63-827f-7e3a133a125c
-- title:
--   Monotone Metric Family: uniform Scalar eq uniform Scalar two
-- statement:
--   The Monotone Metric Family construction uses the uniform Scalar eq uniform Scalar two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/UniformScalarConstant.lean#L220-L243
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/UniformScalarConstant.lean#L220-L243

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

theorem LeanPool.CencovPetz.MonotoneMetricFamily.uniformScalar_eq_uniformScalar_two (G : MonotoneMetricFamily) {n : ℕ} (hn : 2 ≤ n) :
    uniformScalar G n hn = uniformScalar G 2 (by decide) := by sorry
