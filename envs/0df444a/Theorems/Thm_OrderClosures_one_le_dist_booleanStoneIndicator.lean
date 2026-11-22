-- Prove2me | Theorems.Thm_OrderClosures_one_le_dist_booleanStoneIndicator
-- name    : OrderClosures.one_le_dist_booleanStoneIndicator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:00:13.34353+00:00
-- url     : https://prove2.me/theorems/16062bc8-8cc5-4dd6-b65f-2ed38a75521e
-- title:
--   Order Closures: one le dist boolean Stone Indicator
-- statement:
--   Shows distinct Boolean elements give indicators at distance at least one;
--   used to obtain a large separated family.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L1533-L1550
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L1533-L1550

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

theorem OrderClosures.one_le_dist_booleanStoneIndicator
    (B : Type u) [CompleteBooleanAlgebra B] {a b : B} (hab : a ≠ b) :
    (1 : ℝ) ≤ dist (booleanStoneIndicator B a) (booleanStoneIndicator B b) := by sorry
