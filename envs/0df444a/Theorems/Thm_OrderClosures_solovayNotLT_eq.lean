-- Prove2me | Theorems.Thm_OrderClosures_solovayNotLT_eq
-- name    : OrderClosures.solovayNotLT_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:56:25.414153+00:00
-- url     : https://prove2.me/theorems/36b6111e-3036-4fe7-9ced-280be84f84b4
-- title:
--   Order Closures: solovay Not LT eq
-- statement:
--   Computes the complementary order event; used to build exact coordinate
--   conditions from the Solovay generators.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L335-L341
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L335-L341

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
universe u
variable (Gamma : Type u) [LinearOrder Gamma] [TopologicalSpace Gamma]
  [DiscreteTopology Gamma]

theorem OrderClosures.solovayNotLT_eq (m : ℕ) (eta : Gamma) :
    solovayNotLT Gamma m eta = (solovayLT Gamma m eta)ᶜ := by sorry
