-- Prove2me | Theorems.Thm_OrderClosures_uoAdherence_eq_double_orderAdherence_and_stabilizes
-- name    : OrderClosures.uoAdherence_eq_double_orderAdherence_and_stabilizes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:55:34.280128+00:00
-- url     : https://prove2.me/theorems/3e86cd39-8054-44ef-bc90-8cbf1ca66647
-- title:
--   Order Closures: uo Adherence eq double order Adherence and stabilizes
-- statement:
--   The remaining equalities and stabilization stated after Gao--Leung Lemma 2.1.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/OrderAdherence.lean#L318-L335
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/OrderAdherence.lean#L318-L335

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

theorem OrderClosures.uoAdherence_eq_double_orderAdherence_and_stabilizes
    {Y : VectorSublattice X} (hY : IsOrderClosed (uoAdherence (Y : Set X))) :
    uoAdherence (Y : Set X) = orderAdherence (orderAdherence (Y : Set X)) ∧
      orderAdherence (orderAdherence (orderAdherence (Y : Set X))) =
        orderAdherence (orderAdherence (Y : Set X)) := by sorry
