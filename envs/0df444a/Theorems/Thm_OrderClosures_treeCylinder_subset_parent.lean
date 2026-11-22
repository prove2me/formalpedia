-- Prove2me | Theorems.Thm_OrderClosures_treeCylinder_subset_parent
-- name    : OrderClosures.treeCylinder_subset_parent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:05:36.427139+00:00
-- url     : https://prove2.me/theorems/a9383d1c-2174-4ab8-9af9-05d2bcf28a05
-- title:
--   Order Closures: tree Cylinder subset parent
-- statement:
--   Shows that a node cylinder lies inside its parent cylinder; used to prove
--   that upshifting increases the associated tree operator.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/Bands.lean#L273-L294
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/Bands.lean#L273-L294

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

theorem OrderClosures.treeCylinder_subset_parent (n : ℕ) (t : TreeNode n) :
    treeCylinder n t ⊆ treeCylinder n (TreeNode.parent t) := by sorry
