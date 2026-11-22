-- Prove2me | Theorems.Thm_OrderClosures_level_le_of_treeCylinder_subset
-- name    : OrderClosures.level_le_of_treeCylinder_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:04:07.597684+00:00
-- url     : https://prove2.me/theorems/bbf5207b-dbf9-45e4-913a-ee8f341e0a6a
-- title:
--   Order Closures: level le of tree Cylinder subset
-- statement:
--   Shows that inclusion of nonempty tree cylinders forces the corresponding
--   level inequality; used to isolate the maximal-weight basis term.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/TreeNorm.lean#L432-L452
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/TreeNorm.lean#L432-L452

module
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_FiniteTree
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_TreeNorm
set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set Filter Topology
open scoped NNReal Topology
universe u

theorem OrderClosures.level_le_of_treeCylinder_subset {n : ℕ} {t u : TreeNode n}
    (hsub : treeCylinder n t ⊆ treeCylinder n u) :
    TreeNode.level u ≤ TreeNode.level t := by sorry
