-- Prove2me | Theorems.Thm_NormedVectorLattice_continuous_inf
-- name    : NormedVectorLattice.continuous_inf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:13:00.560797+00:00
-- url     : https://prove2.me/theorems/8a4c7bb3-5956-4958-a846-3a8385753a19
-- title:
--   Normed Vector Lattice: continuous inf
-- statement:
--   Infimum is jointly norm-continuous.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Normed.lean#L49-L50
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Normed.lean#L49-L50

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

theorem NormedVectorLattice.continuous_inf : Continuous (fun p : X × X => p.1 ⊓ p.2) := by sorry
