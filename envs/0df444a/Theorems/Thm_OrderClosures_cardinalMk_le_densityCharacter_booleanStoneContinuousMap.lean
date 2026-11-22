-- Prove2me | Theorems.Thm_OrderClosures_cardinalMk_le_densityCharacter_booleanStoneContinuousMap
-- name    : OrderClosures.cardinalMk_le_densityCharacter_booleanStoneContinuousMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:59:52.506171+00:00
-- url     : https://prove2.me/theorems/a94cac40-2b7e-41be-87c3-044995910ccc
-- title:
--   Order Closures: cardinal Mk le density Character boolean Stone Continuous Map
-- statement:
--   Transfers the size of a Boolean algebra to a lower bound on the density
--   character of its continuous-function lattice.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L1554-L1558
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L1554-L1558

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

theorem OrderClosures.cardinalMk_le_densityCharacter_booleanStoneContinuousMap
    (B : Type u) [CompleteBooleanAlgebra B] :
    Cardinal.mk B ≤ densityCharacter C(BooleanStone B, ℝ) := by sorry
