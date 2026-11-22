-- Prove2me | Theorems.Thm_OrderClosures_finiteTreeSup_nonneg
-- name    : OrderClosures.finiteTreeSup_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:03:44.092035+00:00
-- url     : https://prove2.me/theorems/07a54a4e-ff97-4b6b-8f5f-ac75b4a441a1
-- title:
--   Order Closures: finite Tree Sup nonneg
-- statement:
--   Records positivity of a finite supremum of tree functions; used in the
--   least-upper-bound statement for parent-disjoint families.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/FiniteTree.lean#L305-L310
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/FiniteTree.lean#L305-L310

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

theorem OrderClosures.finiteTreeSup_nonneg (n : ℕ) (F : Finset (TreeNode n)) :
    0 ≤ finiteTreeSup n F := by sorry
