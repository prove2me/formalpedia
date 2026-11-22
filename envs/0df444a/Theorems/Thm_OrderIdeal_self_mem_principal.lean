-- Prove2me | Theorems.Thm_OrderIdeal_self_mem_principal
-- name    : OrderIdeal.self_mem_principal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:27:19.468684+00:00
-- url     : https://prove2.me/theorems/9d7a3d81-c366-4a94-b8c0-8c9e10e2bd88
-- title:
--   Order Ideal: self mem principal
-- statement:
--   The generator belongs to its own principal ideal.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Ideal.lean#L319-L320
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Ideal.lean#L319-L320

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Sublattice
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderUnit
public import Mathlib.Analysis.Normed.Group.Completeness
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Ideal
set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
open OrderIdeal
variable (J : OrderIdeal X)

theorem OrderIdeal.self_mem_principal (a : X) : a ∈ principal a := by sorry
