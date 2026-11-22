-- Prove2me | Theorems.Thm_OrderClosures_treeOperator_le_root_of_nonneg
-- name    : OrderClosures.treeOperator_le_root_of_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:03:59.906352+00:00
-- url     : https://prove2.me/theorems/5d657b63-9e80-4959-bb88-f785c2e62c32
-- title:
--   Order Closures: tree Operator le root of nonneg
-- statement:
--   Dominates a positive tree operator by its total coefficient mass times the
--   root; used in the upper norm comparison.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/TreeNorm.lean#L340-L352
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/TreeNorm.lean#L340-L352

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

theorem OrderClosures.treeOperator_le_root_of_nonneg (n : ℕ) (w : TreeCoefficients n)
    (hw : 0 ≤ w) :
    treeOperator n w ≤
      ((2 : ℝ) ^ n * treeRho n w) • treeFunction n (TreeNode.root n) := by sorry
