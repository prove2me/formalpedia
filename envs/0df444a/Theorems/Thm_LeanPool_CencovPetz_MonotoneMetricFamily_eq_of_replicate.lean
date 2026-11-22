-- Prove2me | Theorems.Thm_LeanPool_CencovPetz_MonotoneMetricFamily_eq_of_replicate
-- name    : LeanPool.CencovPetz.MonotoneMetricFamily.eq_of_replicate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:25:56.225554+00:00
-- url     : https://prove2.me/theorems/de2a4651-5681-497b-988b-7e5eb4d9c8d3
-- title:
--   Monotone Metric Family: eq of replicate
-- statement:
--   The Monotone Metric Family construction uses the eq of replicate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/ReplicationInvariance.lean#L54-L71
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/ReplicationInvariance.lean#L54-L71

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

theorem LeanPool.CencovPetz.MonotoneMetricFamily.eq_of_replicate (G : MonotoneMetricFamily) (m : ℕ) (hm : 0 < m) (p : Simplex α)
    (u v : tangentSpace (α := α)) :
    G.g (α := α × Fin m) ((MarkovMorphism.replicate (α := α) m hm).pushforward p)
        ((MarkovMorphism.replicate (α := α) m hm).tangentPushforward u)
        ((MarkovMorphism.replicate (α := α) m hm).tangentPushforward v)
      = G.g (α := α) p u v := by sorry
