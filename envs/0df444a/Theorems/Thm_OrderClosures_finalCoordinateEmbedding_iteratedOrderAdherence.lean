-- Prove2me | Theorems.Thm_OrderClosures_finalCoordinateEmbedding_iteratedOrderAdherence
-- name    : OrderClosures.finalCoordinateEmbedding_iteratedOrderAdherence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:06:34.50805+00:00
-- url     : https://prove2.me/theorems/ceeb786a-2eba-4221-89b7-0940bc1200b2
-- title:
--   Order Closures: final Coordinate Embedding iterated Order Adherence
-- statement:
--   Transfers membership through every finite adherence stage along a
--   coordinate embedding; used for `finalLargeVector_properties`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/FinalSpace.lean#L486-L507
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/FinalSpace.lean#L486-L507

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

theorem OrderClosures.finalCoordinateEmbedding_iteratedOrderAdherence (n k : ℕ)
    {z : TreeComponent n}
    (hz : z ∈ iteratedOrderAdherence (unitBallFor (componentLatticeNorm n)) k) :
    finalCoordinateEmbedding n z ∈
      iteratedOrderAdherence (unitBallFor finalLatticeNorm) k := by sorry
