-- Prove2me | Theorems.Thm_LatticeSeminorm_isSolid_of_mem_basisSets
-- name    : LatticeSeminorm.isSolid_of_mem_basisSets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:17:22.614124+00:00
-- url     : https://prove2.me/theorems/fa20f13b-1200-4a6f-9b27-1ec95c422754
-- title:
--   Lattice Seminorm: is Solid of mem basis Sets
-- statement:
--   Every basis set of the seminorm family associated to a family of lattice seminorms is solid.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/LatticeSeminorm.lean#L50-L55
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/LatticeSeminorm.lean#L50-L55

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Basic
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Definitions.Def_LeanPool_OrderClosures_BanLat_LatticeSeminorm
set_option autoImplicit true
@[expose] public section
public section
open scoped Topology Pointwise
universe u v
open LatticeSeminorm
variable {E : Type u} [AddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [VectorLattice E]

theorem LatticeSeminorm.isSolid_of_mem_basisSets {ι : Type v} (p : ι → LatticeSeminorm E) {s : Set E}
    (hs : s ∈ (toSeminormFamily p).basisSets) : LatticeOrderedAddCommGroup.IsSolid s := by sorry
