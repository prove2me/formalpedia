-- Prove2me | Theorems.Thm_OrderClosures_level_strictPrefix
-- name    : OrderClosures.level_strictPrefix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:04:09.528886+00:00
-- url     : https://prove2.me/theorems/42b182fa-b0db-4b28-b1a4-73cd6f1c4324
-- title:
--   Order Closures: level strict Prefix
-- statement:
--   Computes the level of a strict prefix; used to compare nodes from nested
--   tree cylinders in the exact-basis proof.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/TreeNorm.lean#L425-L428
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/TreeNorm.lean#L425-L428

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

theorem OrderClosures.level_strictPrefix {n : ℕ} (t : TreeNode n)
    (j : Fin (TreeNode.level t)) :
    TreeNode.level (strictPrefix t j).1 = j := by sorry
