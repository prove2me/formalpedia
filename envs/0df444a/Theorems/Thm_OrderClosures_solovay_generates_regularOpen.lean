-- Prove2me | Theorems.Thm_OrderClosures_solovay_generates_regularOpen
-- name    : OrderClosures.solovay_generates_regularOpen
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:57:11.380807+00:00
-- url     : https://prove2.me/theorems/eed122ba-9dae-4631-9a44-1db09099e167
-- title:
--   Order Closures: solovay generates regular Open
-- statement:
--   Packages the preceding membership argument as complete generation of the
--   regular-open Boolean algebra; used in the Gao counterexample.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L560-L568
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L560-L568

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

theorem OrderClosures.solovay_generates_regularOpen [WellFoundedLT Gamma]
    (L : BooleanSubalgebra (RegularOpen (SolovayProduct Gamma)))
    (hcomplete : IsCompleteBooleanSubalgebra L)
    (hB : ∀ m n, solovayB Gamma m n ∈ L) : L = ⊤ := by sorry
