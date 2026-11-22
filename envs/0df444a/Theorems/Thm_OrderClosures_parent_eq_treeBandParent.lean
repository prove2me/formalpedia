-- Prove2me | Theorems.Thm_OrderClosures_parent_eq_treeBandParent
-- name    : OrderClosures.parent_eq_treeBandParent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:04:34.732928+00:00
-- url     : https://prove2.me/theorems/6695c784-24e0-4940-bd69-b4b19cbdc76e
-- title:
--   Order Closures: parent eq tree Band Parent
-- statement:
--   Identifies a nonroot node's parent with the representative of its band;
--   used to analyze the support of the upshift.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/Bands.lean#L219-L225
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/Bands.lean#L219-L225

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

theorem OrderClosures.parent_eq_treeBandParent (n : ℕ) (t : TreeNode n) :
    TreeNode.parent t = treeBandParent n (treeBandOfNode n t) := by sorry
