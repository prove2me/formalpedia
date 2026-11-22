-- Prove2me | Theorems.Thm_NormedVectorLattice_norm_le_norm_abs_sup_abs_of_mem_Icc
-- name    : NormedVectorLattice.norm_le_norm_abs_sup_abs_of_mem_Icc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:14:37.331526+00:00
-- url     : https://prove2.me/theorems/d66584e6-c906-48cc-b4ee-81460f6c3df3
-- title:
--   Normed Vector Lattice: norm le norm abs sup abs of mem Icc
-- statement:
--   Every element `x ∈ [a, b]` satisfies `‖x‖ ≤ ‖|a| ⊔ |b|‖`. In particular, every
--   order interval is norm-bounded.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Normed.lean#L124-L136
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Normed.lean#L124-L136

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

theorem NormedVectorLattice.norm_le_norm_abs_sup_abs_of_mem_Icc {a b x : X} (hx : x ∈ Set.Icc a b) :
    ‖x‖ ≤ ‖|a| ⊔ |b|‖ := by sorry
