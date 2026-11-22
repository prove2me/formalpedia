-- Prove2me | Theorems.Thm_IsVLDisjoint_smul_left
-- name    : IsVLDisjoint.smul_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:13:26.633899+00:00
-- url     : https://prove2.me/theorems/35728c5d-e5d6-4ec3-98a5-8862a58d25d8
-- title:
--   Is VLDisjoint: smul left
-- statement:
--   Scalar multiplication on the left preserves disjointness.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean#L376-L380
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean#L376-L380

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
set_option autoImplicit true
@[expose] public section
public section
open scoped Topology
open Filter Finset
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]

theorem IsVLDisjoint.smul_left {x y : X} (h : IsVLDisjoint x y) (a : ℝ) :
    IsVLDisjoint (a • x) y := by sorry
