-- Prove2me | Theorems.Thm_IsVLDisjoint_mono_right
-- name    : IsVLDisjoint.mono_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:15:03.659812+00:00
-- url     : https://prove2.me/theorems/cae6065e-402d-4f2e-abc5-20a01d6f0b0c
-- title:
--   Is VLDisjoint: mono right
-- statement:
--   If `|z| ≤ |y|` and `x ⊥ y` then `x ⊥ z`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean#L166-L170
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean#L166-L170

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
set_option autoImplicit true
@[expose] public section
public section
open scoped Topology
open Filter Finset
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]

theorem IsVLDisjoint.mono_right {x y z : X} (h : IsVLDisjoint x y)
    (hzy : |z| ≤ |y|) : IsVLDisjoint x z := by sorry
