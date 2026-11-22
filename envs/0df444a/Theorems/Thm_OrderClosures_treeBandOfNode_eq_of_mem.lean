-- Prove2me | Theorems.Thm_OrderClosures_treeBandOfNode_eq_of_mem
-- name    : OrderClosures.treeBandOfNode_eq_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:02:14.483977+00:00
-- url     : https://prove2.me/theorems/c9f49055-82e5-4e82-825b-c2d9f6e00701
-- title:
--   Order Closures: tree Band Of Node eq of mem
-- statement:
--   Recovers the canonical band from membership in a band support; used to
--   prove uniqueness in the band partition.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/Bands.lean#L77-L88
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/Bands.lean#L77-L88

module
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_TreeNorm
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_Bands
set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set Filter Topology
open scoped NNReal Topology
universe u

theorem OrderClosures.treeBandOfNode_eq_of_mem (n : ℕ) (t : TreeNode n)
    (B : TreeBandIndex n) (ht : t ∈ treeBandSupport n B) :
    treeBandOfNode n t = B := by sorry
