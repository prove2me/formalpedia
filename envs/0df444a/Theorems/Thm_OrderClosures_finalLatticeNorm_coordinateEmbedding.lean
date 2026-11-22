-- Prove2me | Theorems.Thm_OrderClosures_finalLatticeNorm_coordinateEmbedding
-- name    : OrderClosures.finalLatticeNorm_coordinateEmbedding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:04:03.812703+00:00
-- url     : https://prove2.me/theorems/3187b1c1-af4e-40ee-85c2-a5c8ae73b723
-- title:
--   Order Closures: final Lattice Norm coordinate Embedding
-- statement:
--   Shows that single-coordinate inclusion is isometric; used to transfer the
--   component large-vector norm to the final space.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/FinalSpace.lean#L411-L425
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/FinalSpace.lean#L411-L425

module
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_Moderated
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_FinalSpace
set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set Filter Topology
open scoped NNReal Topology
universe u

theorem OrderClosures.finalLatticeNorm_coordinateEmbedding (n : ℕ) (z : TreeComponent n) :
    finalLatticeNorm (finalCoordinateEmbedding n z) = componentLatticeNorm n z := by sorry
