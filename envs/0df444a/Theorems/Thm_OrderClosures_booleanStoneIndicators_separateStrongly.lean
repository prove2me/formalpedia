-- Prove2me | Theorems.Thm_OrderClosures_booleanStoneIndicators_separateStrongly
-- name    : OrderClosures.booleanStoneIndicators_separateStrongly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:58:44.179535+00:00
-- url     : https://prove2.me/theorems/7a689fb2-0673-41ff-bf9b-794b302ba54c
-- title:
--   Order Closures: boolean Stone Indicators separate Strongly
-- statement:
--   Produces a Boolean indicator separating two distinct Stone points; used
--   in the lattice Stone--Weierstrass argument.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L1440-L1471
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L1440-L1471

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

theorem OrderClosures.booleanStoneIndicators_separateStrongly
    (Z : VectorSublattice C(BooleanStone B, ℝ))
    (hOne : (1 : C(BooleanStone B, ℝ)) ∈ Z)
    (hIndicator : ∀ b, booleanStoneIndicator B b ∈ Z) :
    (Z : Set C(BooleanStone B, ℝ)).SeparatesPointsStrongly := by sorry
