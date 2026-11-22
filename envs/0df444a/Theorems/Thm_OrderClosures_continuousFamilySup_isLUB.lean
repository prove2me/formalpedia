-- Prove2me | Theorems.Thm_OrderClosures_continuousFamilySup_isLUB
-- name    : OrderClosures.continuousFamilySup_isLUB
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:57:30.072+00:00
-- url     : https://prove2.me/theorems/89d7ddce-7445-445e-af71-f91356301a6e
-- title:
--   Order Closures: continuous Family Sup is LUB
-- statement:
--   Verifies that the constructed continuous function is the least upper bound
--   of the family; used to prove order completeness of `C(K, ℝ)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L1053-L1073
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L1053-L1073

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
variable (K : Type u) [TopologicalSpace K] [ExtremallyDisconnected K]

theorem OrderClosures.continuousFamilySup_isLUB (A : Set C(K, ℝ))
    (hA : A.Nonempty) (hAbdd : BddAbove A) :
    IsLUB A (continuousFamilySup K A hA hAbdd) := by sorry
