-- Prove2me | Theorems.Thm_IsVLDisjoint_smul_right
-- name    : IsVLDisjoint.smul_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:13:30.832114+00:00
-- url     : https://prove2.me/theorems/72b91f26-3f84-4241-97f4-b078d79e454d
-- title:
--   Is VLDisjoint: smul right
-- statement:
--   Scalar multiplication on the right preserves disjointness.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean#L383-L385
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean#L383-L385

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

theorem IsVLDisjoint.smul_right {x y : X} (h : IsVLDisjoint x y) (a : ℝ) :
    IsVLDisjoint x (a • y) := by sorry
