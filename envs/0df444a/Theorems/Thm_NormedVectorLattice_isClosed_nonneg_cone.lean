-- Prove2me | Theorems.Thm_NormedVectorLattice_isClosed_nonneg_cone
-- name    : NormedVectorLattice.isClosed_nonneg_cone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:16:26.497054+00:00
-- url     : https://prove2.me/theorems/0667dd6f-1ca1-4e6d-8c8f-f04f3ec54bf9
-- title:
--   Normed Vector Lattice: is Closed nonneg cone
-- statement:
--   The positive cone `{x | 0 ≤ x}` is norm-closed.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Normed.lean#L91-L91
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Normed.lean#L91-L91

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

theorem NormedVectorLattice.isClosed_nonneg_cone : IsClosed {x : X | 0 ≤ x} := by sorry
