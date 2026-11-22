-- Prove2me | Theorems.Thm_NormedVectorLattice_continuous_sup
-- name    : NormedVectorLattice.continuous_sup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:12:58.120228+00:00
-- url     : https://prove2.me/theorems/9d3eeafd-68c8-4e56-b4cf-ca6710a7872d
-- title:
--   Normed Vector Lattice: continuous sup
-- statement:
--   Supremum is jointly norm-continuous.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Normed.lean#L45-L46
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Normed.lean#L45-L46

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

theorem NormedVectorLattice.continuous_sup : Continuous (fun p : X × X => p.1 ⊔ p.2) := by sorry
