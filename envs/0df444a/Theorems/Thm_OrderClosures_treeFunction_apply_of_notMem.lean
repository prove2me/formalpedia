-- Prove2me | Theorems.Thm_OrderClosures_treeFunction_apply_of_notMem
-- name    : OrderClosures.treeFunction_apply_of_notMem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:56:38.564809+00:00
-- url     : https://prove2.me/theorems/dec5d91c-3eb9-4f0f-a010-c998ed8e2119
-- title:
--   Order Closures: tree Function apply of not Mem
-- statement:
--   Evaluates a tree function off its supporting cylinder; used to show finite
--   tree sums vanish outside their cylinder union.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/FiniteTree.lean#L168-L171
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/FiniteTree.lean#L168-L171

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

theorem OrderClosures.treeFunction_apply_of_notMem (n : ℕ) (t : TreeNode n)
    {α : TreeProduct n} (hα : α ∉ treeCylinder n t) : treeFunction n t α = 0 := by sorry
