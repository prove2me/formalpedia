-- Prove2me | Theorems.Thm_OrderClosures_booleanSubalgebraInVectorSublattice_complete
-- name    : OrderClosures.booleanSubalgebraInVectorSublattice_complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:57:46.573595+00:00
-- url     : https://prove2.me/theorems/cc02d005-862f-4206-b534-6ce4c158fa4a
-- title:
--   Order Closures: boolean Subalgebra In Vector Sublattice complete
-- statement:
--   Shows that Boolean elements whose indicators lie in a vector sublattice
--   form a complete Boolean subalgebra; used with Solovay generation for maximality.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L1263-L1335
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L1263-L1335

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
variable (B : Type u) [CompleteBooleanAlgebra B]

theorem OrderClosures.booleanSubalgebraInVectorSublattice_complete
    (Z : VectorSublattice C(BooleanStone B, ℝ))
    (hOne : (1 : C(BooleanStone B, ℝ)) ∈ Z)
    (hZclosed : IsOrderClosed (Z : Set C(BooleanStone B, ℝ))) :
    IsCompleteBooleanSubalgebra
      (booleanSubalgebraInVectorSublattice B Z hOne) := by sorry
