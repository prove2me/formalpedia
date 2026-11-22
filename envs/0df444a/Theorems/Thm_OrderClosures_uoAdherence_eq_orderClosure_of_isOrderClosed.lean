-- Prove2me | Theorems.Thm_OrderClosures_uoAdherence_eq_orderClosure_of_isOrderClosed
-- name    : OrderClosures.uoAdherence_eq_orderClosure_of_isOrderClosed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:55:31.510359+00:00
-- url     : https://prove2.me/theorems/9aec97e2-7a12-44d8-a6ff-93775ace7b3d
-- title:
--   Order Closures: uo Adherence eq order Closure of is Order Closed
-- statement:
--   If the uo-adherence is order closed, it is the order closure.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/OrderAdherence.lean#L298-L315
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/OrderAdherence.lean#L298-L315

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Pi
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderContinuous_MeyerNieberg
public import Definitions.Def_LeanPool_OrderClosures_BanLat_LatticeSeminorm
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Sublattice
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Tactic_LLexpr
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Examples_CofK_Basic
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Operators_Hom
public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.SetTheory.Ordinal.Arithmetic
public import Definitions.Def_LeanPool_OrderClosures_OrderAdherence
set_option autoImplicit true
@[expose] public section
public section
open Set
open OrderClosures
universe u v
variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]

theorem OrderClosures.uoAdherence_eq_orderClosure_of_isOrderClosed {Y : VectorSublattice X}
    (hY : IsOrderClosed (uoAdherence (Y : Set X))) :
    uoAdherence (Y : Set X) = orderClosure (Y : Set X) := by sorry
