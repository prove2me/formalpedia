-- Prove2me | Theorems.Thm_OrderIdeal_subset_generated
-- name    : OrderIdeal.subset_generated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:27:28.886487+00:00
-- url     : https://prove2.me/theorems/9bdddbc1-51d9-4e79-9734-36e55008cc0b
-- title:
--   Order Ideal: subset generated
-- statement:
--   The set `s` is contained in the ideal it generates.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Ideal.lean#L179-L180
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Ideal.lean#L179-L180

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Sublattice
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderUnit
public import Mathlib.Analysis.Normed.Group.Completeness
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Ideal
public import Theorems.Thm_VectorSublattice_subset_generated

set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
open OrderIdeal
variable (J : OrderIdeal X)

theorem OrderIdeal.subset_generated (s : Set X) : s ⊆ (generated s : Set X) := by sorry
