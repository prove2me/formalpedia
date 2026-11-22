-- Prove2me | Theorems.Thm_IsVLDisjoint_add_right
-- name    : IsVLDisjoint.add_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:13:34.265448+00:00
-- url     : https://prove2.me/theorems/0551c88e-670e-4e8d-820c-e9daaf5313b4
-- title:
--   Is VLDisjoint: add right
-- statement:
--   If `x ⊥ y` and `x ⊥ z` then `x ⊥ y + z`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean#L251-L258
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean#L251-L258

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
set_option autoImplicit true
@[expose] public section
public section
open scoped Topology
open Filter Finset
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]

theorem IsVLDisjoint.add_right {x y z : X}
    (hy : IsVLDisjoint x y) (hz : IsVLDisjoint x z) :
    IsVLDisjoint x (y + z) := by sorry
