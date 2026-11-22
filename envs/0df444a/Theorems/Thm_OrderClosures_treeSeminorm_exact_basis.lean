-- Prove2me | Theorems.Thm_OrderClosures_treeSeminorm_exact_basis
-- name    : OrderClosures.treeSeminorm_exact_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:04:16.144477+00:00
-- url     : https://prove2.me/theorems/3cc42615-18dd-4f51-aae9-0f91635daa78
-- title:
--   Order Closures: tree Seminorm exact basis
-- statement:
--   Paper Lemma `lem:exact-basis`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/TreeNorm.lean#L466-L536
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/TreeNorm.lean#L466-L536

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

theorem OrderClosures.treeSeminorm_exact_basis (n : ℕ) (t : TreeNode n) :
    (∀ w : TreeCoefficients n, 0 ≤ w → treeFunction n t ≤ treeOperator n w →
      (2 : ℝ) ^ (-(TreeNode.level t : ℤ)) ≤ treeRho n w) ∧
    treeSeminorm n (treeFunction n t) =
      (2 : ℝ) ^ (-(TreeNode.level t : ℤ)) := by sorry
