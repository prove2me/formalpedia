-- Prove2me | Theorems.Thm_OrderClosures_finiteTreeSup_apply_of_notMem
-- name    : OrderClosures.finiteTreeSup_apply_of_notMem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:03:44.310163+00:00
-- url     : https://prove2.me/theorems/c410c38f-18e2-4b05-a67e-f7d882d8be40
-- title:
--   Order Closures: finite Tree Sup apply of not Mem
-- statement:
--   Shows that a finite tree supremum vanishes outside its cylinder union;
--   used in the common-lower-bound argument.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/FiniteTree.lean#L314-L318
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/FiniteTree.lean#L314-L318

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

theorem OrderClosures.finiteTreeSup_apply_of_notMem (n : ℕ) (F : Finset (TreeNode n))
    {α : TreeProduct n} (hα : α ∉ finiteCylinderUnion n F) :
    finiteTreeSup n F α = 0 := by sorry
