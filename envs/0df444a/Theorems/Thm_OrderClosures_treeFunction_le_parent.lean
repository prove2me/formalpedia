-- Prove2me | Theorems.Thm_OrderClosures_treeFunction_le_parent
-- name    : OrderClosures.treeFunction_le_parent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:05:30.74299+00:00
-- url     : https://prove2.me/theorems/0c0c0074-6b5e-40d8-9153-424444f78c2b
-- title:
--   Order Closures: tree Function le parent
-- statement:
--   Converts cylinder inclusion into domination by the parent tree function;
--   used in `treeUpshift_basic`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/Bands.lean#L298-L306
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/Bands.lean#L298-L306

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

theorem OrderClosures.treeFunction_le_parent (n : ℕ) (t : TreeNode n) :
    treeFunction n t ≤ treeFunction n (TreeNode.parent t) := by sorry
