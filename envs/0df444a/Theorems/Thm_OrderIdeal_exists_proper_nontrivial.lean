-- Prove2me | Theorems.Thm_OrderIdeal_exists_proper_nontrivial
-- name    : OrderIdeal.exists_proper_nontrivial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:28:00.718898+00:00
-- url     : https://prove2.me/theorems/74c6c631-f292-4c94-af83-926ca3d7e556
-- title:
--   Order Ideal: exists proper nontrivial
-- statement:
--   If the real dimension of `X` is strictly greater than one, then `X` admits
--   an order ideal that is **neither trivial nor the whole space**.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Ideal.lean#L865-L879
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Ideal.lean#L865-L879

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
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
variable (a : X)

theorem OrderIdeal.exists_proper_nontrivial [IsVLArchimedean X] (h : 1 < Module.rank ℝ X) :
    ∃ J : OrderIdeal X, J ≠ ⊥ ∧ J ≠ ⊤ := by sorry
