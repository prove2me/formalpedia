-- Prove2me | Theorems.Thm_OrderClosures_treeFunction_nonneg
-- name    : OrderClosures.treeFunction_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:01:06.728558+00:00
-- url     : https://prove2.me/theorems/7ed57342-f8b0-421a-9dff-a0d431862498
-- title:
--   Order Closures: tree Function nonneg
-- statement:
--   Records positivity of every tree function; used for lattice estimates and
--   for the positive terminal family in the component construction.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/TreeNorm.lean#L456-L463
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/TreeNorm.lean#L456-L463

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

theorem OrderClosures.treeFunction_nonneg (n : ℕ) (t : TreeNode n) :
    0 ≤ treeFunction n t := by sorry
