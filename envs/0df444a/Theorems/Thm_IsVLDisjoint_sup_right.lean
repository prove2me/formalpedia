-- Prove2me | Theorems.Thm_IsVLDisjoint_sup_right
-- name    : IsVLDisjoint.sup_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:15:11.558811+00:00
-- url     : https://prove2.me/theorems/bf06ad96-b7c9-4fe7-a998-f69db054ee06
-- title:
--   Is VLDisjoint: sup right
-- statement:
--   If `x ⊥ y` and `x ⊥ z` then `x ⊥ y ⊔ z`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean#L232-L248
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean#L232-L248

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
set_option autoImplicit true
@[expose] public section
public section
open scoped Topology
open Filter Finset
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]

theorem IsVLDisjoint.sup_right {x y z : X}
    (hy : IsVLDisjoint x y) (hz : IsVLDisjoint x z) :
    IsVLDisjoint x (y ⊔ z) := by sorry
