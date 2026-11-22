-- Prove2me | Theorems.Thm_OrderClosures_treeParent_weight_le
-- name    : OrderClosures.treeParent_weight_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:05:24.244797+00:00
-- url     : https://prove2.me/theorems/224ec4d3-3d8e-4769-a425-1ddb28594920
-- title:
--   Order Closures: tree Parent weight le
-- statement:
--   Compares the weight of a parent node with that of its child; used to bound
--   the `treeRho` cost of upshifting.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/Bands.lean#L259-L269
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/Bands.lean#L259-L269

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

theorem OrderClosures.treeParent_weight_le (n : ℕ) (t : TreeNode n) :
    (2 : ℝ) ^ (-(TreeNode.level (TreeNode.parent t) : ℤ)) ≤
      2 * (2 : ℝ) ^ (-(TreeNode.level t : ℤ)) := by sorry
