-- Prove2me | Theorems.Thm_OrderClosures_orderAdherence_mono
-- name    : OrderClosures.orderAdherence_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:55:25.037262+00:00
-- url     : https://prove2.me/theorems/0723bbc7-e74a-4492-a2c6-8aaef1c0d8b7
-- title:
--   Order Closures: order Adherence mono
-- statement:
--   Order adherence is monotone.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/OrderAdherence.lean#L188-L191
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/OrderAdherence.lean#L188-L191

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
omit [IsOrderedAddMonoid X] [VectorLattice X]

theorem OrderClosures.orderAdherence_mono : Monotone (orderAdherence : Set X → Set X) := by sorry
