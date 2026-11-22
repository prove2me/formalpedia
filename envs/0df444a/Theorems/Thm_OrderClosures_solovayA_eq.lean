-- Prove2me | Theorems.Thm_OrderClosures_solovayA_eq
-- name    : OrderClosures.solovayA_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:57:03.783558+00:00
-- url     : https://prove2.me/theorems/e4772518-6cb2-41ba-a30a-4d5c686df56a
-- title:
--   Order Closures: solovay A eq
-- statement:
--   Gives the fundamental Boolean identity for a Solovay generator; used to
--   recover exact coordinate cylinders.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L415-L423
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L415-L423

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

theorem OrderClosures.solovayA_eq (n : ℕ) (eta : Gamma) :
    solovayA Gamma n eta =
      solovayLE Gamma n eta ⊓ (solovayLT Gamma n eta)ᶜ := by sorry
