-- Prove2me | Theorems.Thm_OrderClosures_treeFunction_apply_of_mem
-- name    : OrderClosures.treeFunction_apply_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:56:32.890803+00:00
-- url     : https://prove2.me/theorems/07ee7387-2084-4958-af27-217cc4f5e374
-- title:
--   Order Closures: tree Function apply of mem
-- statement:
--   Evaluates a tree function on its supporting cylinder; used in the exact
--   basis and tree-operator computations.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/FiniteTree.lean#L161-L164
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/FiniteTree.lean#L161-L164

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

theorem OrderClosures.treeFunction_apply_of_mem (n : ℕ) (t : TreeNode n)
    {α : TreeProduct n} (hα : α ∈ treeCylinder n t) : treeFunction n t α = 1 := by sorry
