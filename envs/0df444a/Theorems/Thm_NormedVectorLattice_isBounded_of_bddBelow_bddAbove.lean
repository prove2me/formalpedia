-- Prove2me | Theorems.Thm_NormedVectorLattice_isBounded_of_bddBelow_bddAbove
-- name    : NormedVectorLattice.isBounded_of_bddBelow_bddAbove
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:16:36.751798+00:00
-- url     : https://prove2.me/theorems/7f71b33e-931f-4e45-be3c-7d7f707c7a29
-- title:
--   Normed Vector Lattice: is Bounded of bdd Below bdd Above
-- statement:
--   Order-bounded sets are norm-bounded.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Normed.lean#L139-L146
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Normed.lean#L139-L146

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Basic
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Topology.Order.MonotoneConvergence
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
set_option autoImplicit true
@[expose] public section
public section
open NormedVectorLattice
variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [NormedVectorLattice X]

theorem NormedVectorLattice.isBounded_of_bddBelow_bddAbove {s : Set X}
    (hl : BddBelow s) (hu : BddAbove s) : Bornology.IsBounded s := by sorry
