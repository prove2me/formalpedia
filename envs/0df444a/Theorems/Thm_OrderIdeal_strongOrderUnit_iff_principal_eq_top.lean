-- Prove2me | Theorems.Thm_OrderIdeal_strongOrderUnit_iff_principal_eq_top
-- name    : OrderIdeal.strongOrderUnit_iff_principal_eq_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:28:08.905928+00:00
-- url     : https://prove2.me/theorems/a028a6f0-7300-49cd-b104-6b5002ffecf3
-- title:
--   Order Ideal: strong Order Unit iff principal eq top
-- statement:
--   An element is a strong order unit precisely when it is non-negative and the
--   principal ideal it generates is the whole space.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Ideal.lean#L831-L839
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Ideal.lean#L831-L839

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

theorem OrderIdeal.strongOrderUnit_iff_principal_eq_top {e : X} :
    StrongOrderUnit e ↔ 0 ≤ e ∧ principal e = ⊤ := by sorry
