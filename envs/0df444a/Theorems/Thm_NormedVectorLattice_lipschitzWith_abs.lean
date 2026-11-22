-- Prove2me | Theorems.Thm_NormedVectorLattice_lipschitzWith_abs
-- name    : NormedVectorLattice.lipschitzWith_abs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:13:04.226306+00:00
-- url     : https://prove2.me/theorems/289f7e06-866d-47ba-b3af-34cb94be5985
-- title:
--   Normed Vector Lattice: lipschitz With abs
-- statement:
--   The absolute value map is Lipschitz with constant 1; in particular it is continuous.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Normed.lean#L53-L56
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Normed.lean#L53-L56

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

theorem NormedVectorLattice.lipschitzWith_abs : LipschitzWith 1 (|·| : X → X) := by sorry
