-- Prove2me | Theorems.Thm_OrderClosures_solovayA_injective
-- name    : OrderClosures.solovayA_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:57:26.520795+00:00
-- url     : https://prove2.me/theorems/50d4f213-e392-4b7e-a181-8779a39a1577
-- title:
--   Order Closures: solovay A injective
-- statement:
--   Shows one coordinate layer of Solovay generators is injectively indexed;
--   used for the density-character lower bound.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L572-L583
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L572-L583

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

theorem OrderClosures.solovayA_injective (n : ℕ) : Function.Injective (solovayA Gamma n) := by sorry
