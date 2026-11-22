-- Prove2me | Theorems.Thm_IsVLDisjoint_mono_left
-- name    : IsVLDisjoint.mono_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:13:25.992056+00:00
-- url     : https://prove2.me/theorems/dec0f55a-8c8e-42e5-a2af-8ca1f06aff4e
-- title:
--   Is VLDisjoint: mono left
-- statement:
--   If `|z| ≤ |x|` and `x ⊥ y` then `z ⊥ y`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean#L173-L175
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean#L173-L175

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
set_option autoImplicit true
@[expose] public section
public section
open scoped Topology
open Filter Finset
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]

theorem IsVLDisjoint.mono_left {x y z : X} (h : IsVLDisjoint x y)
    (hzx : |z| ≤ |x|) : IsVLDisjoint z y := by sorry
