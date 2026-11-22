-- Prove2me | Theorems.Thm_LeanPool_CencovPetz_MonotoneMetricFamily_comp_eq_of_replicate
-- name    : LeanPool.CencovPetz.MonotoneMetricFamily.comp_eq_of_replicate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:26:05.85982+00:00
-- url     : https://prove2.me/theorems/630ee7d9-c0f0-4083-b214-98c477865751
-- title:
--   Monotone Metric Family: comp eq of replicate
-- statement:
--   The Monotone Metric Family construction uses the comp eq of replicate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/ReplicationInvariance.lean#L36-L52
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/ReplicationInvariance.lean#L36-L52

module
public import Definitions.Def_LeanPool_CencovPetz_Replication
public import Definitions.Def_LeanPool_CencovPetz_MonotoneMetric
public import Mathlib.LinearAlgebra.BilinearForm.Hom
public import Definitions.Def_LeanPool_CencovPetz_LeftInverseIsometry
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Definitions.Def_LeanPool_CencovPetz_ReplicationInvariance
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.CencovPetz
open scoped BigOperators
universe u
variable {α : Type u} [Fintype α]
open LeanPool.CencovPetz.MonotoneMetricFamily

theorem LeanPool.CencovPetz.MonotoneMetricFamily.comp_eq_of_replicate (G : MonotoneMetricFamily) (m : ℕ) (hm : 0 < m) (p : Simplex α) :
    (G.g (α := α × Fin m) ((MarkovMorphism.replicate (α := α) m hm).pushforward p)).comp
        ((MarkovMorphism.replicate (α := α) m hm).tangentPushforwardLinear)
        ((MarkovMorphism.replicate (α := α) m hm).tangentPushforwardLinear)
      = G.g (α := α) p := by sorry
