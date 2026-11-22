-- Prove2me | Theorems.Thm_NormedVectorLattice_isClosed_interval
-- name    : NormedVectorLattice.isClosed_interval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:16:35.408585+00:00
-- url     : https://prove2.me/theorems/daa2fd66-7cb1-4b92-9ee0-d3329f3c373d
-- title:
--   Normed Vector Lattice: is Closed interval
-- statement:
--   Order intervals are norm-closed.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Normed.lean#L120-L120
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Normed.lean#L120-L120

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

theorem NormedVectorLattice.isClosed_interval (a b : X) : IsClosed (Set.Icc a b) := by sorry
