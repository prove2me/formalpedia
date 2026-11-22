-- Prove2me | Theorems.Thm_LeanPool_CencovPetz_MonotoneMetricFamily_eq_of_left_inverse
-- name    : LeanPool.CencovPetz.MonotoneMetricFamily.eq_of_left_inverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:25:37.807816+00:00
-- url     : https://prove2.me/theorems/36b02be4-9331-4f3c-bf64-ea89b8e34525
-- title:
--   Monotone Metric Family: eq of left inverse
-- statement:
--   The Monotone Metric Family construction uses the eq of left inverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/LeftInverseIsometry.lean#L76-L85
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/LeftInverseIsometry.lean#L76-L85

module
public import Definitions.Def_LeanPool_CencovPetz_MonotoneMetric
public import Mathlib.LinearAlgebra.BilinearForm.Hom
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Complex.Order
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Definitions.Def_LeanPool_CencovPetz_LeftInverseIsometry
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.CencovPetz
open scoped BigOperators
universe u
open LeanPool.CencovPetz.MonotoneMetricFamily

theorem LeanPool.CencovPetz.MonotoneMetricFamily.eq_of_left_inverse (G : MonotoneMetricFamily) {α β : Type u} [Fintype α] [Fintype β]
    (κ : MarkovMorphism α β) (κ' : MarkovMorphism β α) (p : Simplex α)
    (hp : κ'.pushforward (κ.pushforward p) = p)
    (ht : ∀ u : tangentSpace (α := α), κ'.tangentPushforward (κ.tangentPushforward u) = u)
    (u v : tangentSpace (α := α)) :
    G.g (α := β) (κ.pushforward p) (κ.tangentPushforward u) (κ.tangentPushforward v) =
      G.g (α := α) p u v := by sorry
