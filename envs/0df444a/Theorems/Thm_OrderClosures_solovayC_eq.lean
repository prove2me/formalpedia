-- Prove2me | Theorems.Thm_OrderClosures_solovayC_eq
-- name    : OrderClosures.solovayC_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:56:58.96518+00:00
-- url     : https://prove2.me/theorems/c36ae45a-5dc5-4ffb-acc1-800202f5d47b
-- title:
--   Order Closures: solovay C eq
-- statement:
--   Gives the Boolean formula for the auxiliary comparison element `solovayC`;
--   used to derive the non-strict order event.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L355-L361
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L355-L361

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

theorem OrderClosures.solovayC_eq (m n : ℕ) (eta : Gamma) :
    solovayC Gamma m n eta = (solovayBad Gamma m n eta)ᶜ := by sorry
