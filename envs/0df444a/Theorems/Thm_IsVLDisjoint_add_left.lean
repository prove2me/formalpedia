-- Prove2me | Theorems.Thm_IsVLDisjoint_add_left
-- name    : IsVLDisjoint.add_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:13:36.892957+00:00
-- url     : https://prove2.me/theorems/1a39343b-9831-43c4-b9f2-99ca8523a4ae
-- title:
--   Is VLDisjoint: add left
-- statement:
--   If `x ⊥ z` and `y ⊥ z` then `x + y ⊥ z`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean#L268-L272
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean#L268-L272

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
set_option autoImplicit true
@[expose] public section
public section
open scoped Topology
open Filter Finset
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]

theorem IsVLDisjoint.add_left {x y z : X}
    (hx : IsVLDisjoint x z) (hy : IsVLDisjoint y z) :
    IsVLDisjoint (x + y) z := by sorry
