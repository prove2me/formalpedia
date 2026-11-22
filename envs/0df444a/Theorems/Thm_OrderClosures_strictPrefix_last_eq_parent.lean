-- Prove2me | Theorems.Thm_OrderClosures_strictPrefix_last_eq_parent
-- name    : OrderClosures.strictPrefix_last_eq_parent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:03:39.195596+00:00
-- url     : https://prove2.me/theorems/7a8ecb4a-c0cf-41d1-907f-87fc506316a2
-- title:
--   Order Closures: strict Prefix last eq parent
-- statement:
--   Identifies the last strict prefix with the parent of a nonroot node; used
--   when constructing points outside parent-disjoint cylinder families.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/FiniteTree.lean#L290-L301
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/FiniteTree.lean#L290-L301

module
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_Reductions
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_FiniteTree
set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set Filter Topology
open scoped NNReal Topology
universe u

theorem OrderClosures.strictPrefix_last_eq_parent {n : ℕ} (t : TreeNode n)
    (ht : 0 < TreeNode.level t) :
    let j : Fin (TreeNode.level t) :=
      ⟨TreeNode.level t - 1, Nat.sub_lt ht (by omega)⟩
    (strictPrefix t j).1 = TreeNode.parent t ∧ t.1.get j = treeLastLabel t := by sorry
