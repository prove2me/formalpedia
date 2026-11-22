-- Prove2me | Theorems.Thm_OrderClosures_treeOperator_mem_treeSublattice
-- name    : OrderClosures.treeOperator_mem_treeSublattice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:04:32.244259+00:00
-- url     : https://prove2.me/theorems/8e8bfedf-958a-4154-8f2d-85937404546b
-- title:
--   Order Closures: tree Operator mem tree Sublattice
-- statement:
--   Places every finitely supported tree operator in the generated closed
--   sublattice; used to turn coefficient majorants into component elements.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/TreeNorm.lean#L545-L555
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/TreeNorm.lean#L545-L555

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

theorem OrderClosures.treeOperator_mem_treeSublattice (n : ℕ) (w : TreeCoefficients n) :
    treeOperator n w ∈ treeSublattice n := by sorry
