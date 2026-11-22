-- Prove2me | Theorems.Thm_OrderClosures_mem_treeCylinder_child_iff
-- name    : OrderClosures.mem_treeCylinder_child_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:03:37.09681+00:00
-- url     : https://prove2.me/theorems/3e66f214-4b6b-4553-b1e4-de723d8835a9
-- title:
--   Order Closures: mem tree Cylinder child iff
-- statement:
--   Characterizes membership in a child cylinder by the parent coordinates
--   and one new label; used in the cylinder partition proofs.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/FiniteTree.lean#L78-L139
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/FiniteTree.lean#L78-L139

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

theorem OrderClosures.mem_treeCylinder_child_iff
    (n : ℕ) (t : TreeNode n) (ht : TreeNode.level t < n) (m : ℕ)
    (α : TreeProduct n) :
    α ∈ treeCylinder n (TreeNode.child t ht m) ↔
      α ∈ treeCylinder n t ∧ α ⟨t, ht⟩ ≤ m := by sorry
