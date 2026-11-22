-- Prove2me | Theorems.Thm_OrderClosures_vectorSublattice_eq_top_of_booleanStoneIndicators
-- name    : OrderClosures.vectorSublattice_eq_top_of_booleanStoneIndicators
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:00:13.55306+00:00
-- url     : https://prove2.me/theorems/4d0ba17d-58a3-418b-8706-758ab74507a9
-- title:
--   Order Closures: vector Sublattice eq top of boolean Stone Indicators
-- statement:
--   Shows that a closed vector sublattice containing every Boolean indicator
--   is all of `C(K, ℝ)`; used to prove maximality of the Solovay sublattice.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L1475-L1496
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L1475-L1496

module
public import Definitions.Def_LeanPool_OrderClosures_OrderAdherence
public import Mathlib.Order.Heyting.Regular
public import Mathlib.Order.BooleanSubalgebra
public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.Topology.Category.Stonean.Basic
public import Mathlib.Order.PrimeSeparator
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Definitions.Def_LeanPool_OrderClosures_Solovay
set_option autoImplicit true
@[expose] public section
public section
open Set
noncomputable section
open OrderClosures
universe u v
variable (B : Type u) [CompleteBooleanAlgebra B]

theorem OrderClosures.vectorSublattice_eq_top_of_booleanStoneIndicators
    (Z : VectorSublattice C(BooleanStone B, ℝ))
    (hOne : (1 : C(BooleanStone B, ℝ)) ∈ Z)
    (hIndicator : ∀ b, booleanStoneIndicator B b ∈ Z)
    (hZorder : IsOrderClosed (Z : Set C(BooleanStone B, ℝ))) :
    Z = ⊤ := by sorry
