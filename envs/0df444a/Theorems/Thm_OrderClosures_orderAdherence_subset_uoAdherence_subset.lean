-- Prove2me | Theorems.Thm_OrderClosures_orderAdherence_subset_uoAdherence_subset
-- name    : OrderClosures.orderAdherence_subset_uoAdherence_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:55:22.68799+00:00
-- url     : https://prove2.me/theorems/45a24adf-b4f8-40f9-b974-53d733117973
-- title:
--   Order Closures: order Adherence subset uo Adherence subset
-- statement:
--   Gao--Leung, Lemma 2.1: the two adherences lie within two order-adherence steps.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/OrderAdherence.lean#L264-L295
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/OrderAdherence.lean#L264-L295

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

theorem OrderClosures.orderAdherence_subset_uoAdherence_subset {Y : VectorSublattice X} :
    orderAdherence (Y : Set X) ⊆ uoAdherence (Y : Set X) ∧
      uoAdherence (Y : Set X) ⊆ orderAdherence (orderAdherence (Y : Set X)) := by sorry
