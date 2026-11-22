-- Prove2me | Theorems.Thm_OrderClosures_isSolid_orderAdherence
-- name    : OrderClosures.isSolid_orderAdherence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:55:28.508974+00:00
-- url     : https://prove2.me/theorems/0a3cb5e7-d7cb-4ecb-8cad-67b0851898ef
-- title:
--   Order Closures: is Solid order Adherence
-- statement:
--   The order adherence of a solid set is solid.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/OrderAdherence.lean#L339-L343
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/OrderAdherence.lean#L339-L343

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

theorem OrderClosures.isSolid_orderAdherence {A : Set X}
    (hA : LatticeOrderedAddCommGroup.IsSolid A) :
    LatticeOrderedAddCommGroup.IsSolid (orderAdherence A) := by sorry
