-- Prove2me | Theorems.Thm_OrderClosures_treeFunction_child_properties
-- name    : OrderClosures.treeFunction_child_properties
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:03:39.829955+00:00
-- url     : https://prove2.me/theorems/31592563-b837-43a9-a844-f4b651dc8fe2
-- title:
--   Order Closures: tree Function child properties
-- statement:
--   Paper Lemma `lem:basic-tree`, parts (b) and (c).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/FiniteTree.lean#L183-L233
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/FiniteTree.lean#L183-L233

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

theorem OrderClosures.treeFunction_child_properties
    (n : ℕ) (t : TreeNode n) (ht : TreeNode.level t < n) :
    (∀ m, treeCylinder n (TreeNode.child t ht m) ⊆ treeCylinder n t ∧
      treeFunction n (TreeNode.child t ht m) ≤ treeFunction n t) ∧
    Monotone (fun m ↦ treeFunction n (TreeNode.child t ht m)) ∧
      IsLUB (Set.range fun m ↦ treeFunction n (TreeNode.child t ht m))
        (treeFunction n t) := by sorry
