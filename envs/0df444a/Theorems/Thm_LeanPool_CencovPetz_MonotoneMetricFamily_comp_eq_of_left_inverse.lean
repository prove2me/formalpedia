-- Prove2me | Theorems.Thm_LeanPool_CencovPetz_MonotoneMetricFamily_comp_eq_of_left_inverse
-- name    : LeanPool.CencovPetz.MonotoneMetricFamily.comp_eq_of_left_inverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:25:24.831651+00:00
-- url     : https://prove2.me/theorems/5fc3d064-af07-4b5d-86df-8b2b7400e221
-- title:
--   Monotone Metric Family: comp eq of left inverse
-- statement:
--   The Monotone Metric Family construction uses the comp eq of left inverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/LeftInverseIsometry.lean#L38-L74
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/LeftInverseIsometry.lean#L38-L74

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

theorem LeanPool.CencovPetz.MonotoneMetricFamily.comp_eq_of_left_inverse (G : MonotoneMetricFamily) {α β : Type u} [Fintype α] [Fintype β]
    (κ : MarkovMorphism α β) (κ' : MarkovMorphism β α) (p : Simplex α)
    (hp : κ'.pushforward (κ.pushforward p) = p)
    (ht : ∀ u : tangentSpace (α := α), κ'.tangentPushforward (κ.tangentPushforward u) = u) :
    (G.g (α := β) (κ.pushforward p)).comp κ.tangentPushforwardLinear κ.tangentPushforwardLinear
      = G.g (α := α) p := by sorry
