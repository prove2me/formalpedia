-- Prove2me | Theorems.Thm_OrderClosures_finalCoordinateEmbedding_ne
-- name    : OrderClosures.finalCoordinateEmbedding_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:03:58.21902+00:00
-- url     : https://prove2.me/theorems/ab29ec25-2f2b-4247-9d9d-706c11ac2e71
-- title:
--   Order Closures: final Coordinate Embedding ne
-- statement:
--   Evaluates a single-coordinate embedding away from its chosen coordinate;
--   used in the final lattice and convergence calculations.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/FinalSpace.lean#L193-L195
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/FinalSpace.lean#L193-L195

module
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_Moderated
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_FinalSpace
set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set Filter Topology
open scoped NNReal Topology
universe u

theorem OrderClosures.finalCoordinateEmbedding_ne (n m : ℕ) (h : m ≠ n)
    (z : TreeComponent n) : (finalCoordinateEmbedding n z).1 m = 0 := by sorry
