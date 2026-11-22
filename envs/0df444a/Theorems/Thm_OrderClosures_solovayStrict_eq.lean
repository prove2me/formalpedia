-- Prove2me | Theorems.Thm_OrderClosures_solovayStrict_eq
-- name    : OrderClosures.solovayStrict_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:57:03.586038+00:00
-- url     : https://prove2.me/theorems/9c85c29b-bd5b-48b4-a2b9-9beeaa654ee2
-- title:
--   Order Closures: solovay Strict eq
-- statement:
--   Computes the event that one coordinate is strictly below another; used in
--   the recursive recovery of finite cylinders.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L325-L331
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L325-L331

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

theorem OrderClosures.solovayStrict_eq (m n : ℕ) :
    solovayStrict Gamma m n = (solovayB Gamma n m)ᶜ := by sorry
