-- Prove2me | Theorems.Thm_IsVLDisjoint_sup_left
-- name    : IsVLDisjoint.sup_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:16:58.459795+00:00
-- url     : https://prove2.me/theorems/f2456431-5988-4563-81e0-f6a65408b5ed
-- title:
--   Is VLDisjoint: sup left
-- statement:
--   If `x ⊥ z` and `y ⊥ z` then `x ⊔ y ⊥ z`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean#L261-L265
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean#L261-L265

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
set_option autoImplicit true
@[expose] public section
public section
open scoped Topology
open Filter Finset
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]

theorem IsVLDisjoint.sup_left {x y z : X}
    (hx : IsVLDisjoint x z) (hy : IsVLDisjoint y z) :
    IsVLDisjoint (x ⊔ y) z := by sorry
