-- Prove2me | Theorems.Thm_OrderClosures_orderAdherence_eq_solidOrderAdherence
-- name    : OrderClosures.orderAdherence_eq_solidOrderAdherence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:55:35.229328+00:00
-- url     : https://prove2.me/theorems/59c9cc41-d800-4a9f-8c45-6d8062800c25
-- title:
--   Order Closures: order Adherence eq solid Order Adherence
-- statement:
--   The generic net definition and the directed-positive definition agree for solid sets.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/OrderAdherence.lean#L95-L177
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/OrderAdherence.lean#L95-L177

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
omit [VectorLattice X]

theorem OrderClosures.orderAdherence_eq_solidOrderAdherence {A : Set X}
    (hA : LatticeOrderedAddCommGroup.IsSolid A) :
    orderAdherence A = solidOrderAdherence A := by sorry
