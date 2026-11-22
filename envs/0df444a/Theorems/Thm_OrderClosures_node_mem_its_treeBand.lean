-- Prove2me | Theorems.Thm_OrderClosures_node_mem_its_treeBand
-- name    : OrderClosures.node_mem_its_treeBand
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:02:54.673039+00:00
-- url     : https://prove2.me/theorems/c9041fe9-17fe-419e-8d58-6e6ebe3024ec
-- title:
--   Order Closures: node mem its tree Band
-- statement:
--   Assigns every node to its canonical root or sibling band; used to partition
--   coefficient supports.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/Bands.lean#L68-L73
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/Bands.lean#L68-L73

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

theorem OrderClosures.node_mem_its_treeBand (n : ℕ) (t : TreeNode n) :
    t ∈ treeBandSupport n (treeBandOfNode n t) := by sorry
