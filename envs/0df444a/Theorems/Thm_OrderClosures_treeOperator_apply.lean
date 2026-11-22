-- Prove2me | Theorems.Thm_OrderClosures_treeOperator_apply
-- name    : OrderClosures.treeOperator_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:01:07.587693+00:00
-- url     : https://prove2.me/theorems/ac765b80-d34b-43ef-ab0d-534b83859a3d
-- title:
--   Order Closures: tree Operator apply
-- statement:
--   Expands pointwise evaluation of the tree operator as a finite sum; used in
--   support-vanishing and root estimates.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/TreeNorm.lean#L161-L172
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/TreeNorm.lean#L161-L172

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

theorem OrderClosures.treeOperator_apply (n : ℕ) (w : TreeCoefficients n)
    (α : TreeProduct n) :
    treeOperator n w α = w.sum (fun t a ↦ a * treeFunction n t α) := by sorry
