-- Prove2me | Theorems.Thm_OrderClosures_finalCoordinateEmbedding_orderConverges
-- name    : OrderClosures.finalCoordinateEmbedding_orderConverges
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:06:26.671442+00:00
-- url     : https://prove2.me/theorems/7cfe4095-7ca8-476d-ab4f-79612ee0910d
-- title:
--   Order Closures: final Coordinate Embedding order Converges
-- statement:
--   Shows that single-coordinate inclusion preserves order convergence; used
--   to transfer iterated component adherence into the final space.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/FinalSpace.lean#L429-L482
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/FinalSpace.lean#L429-L482

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

theorem OrderClosures.finalCoordinateEmbedding_orderConverges
    {n : ℕ} {ι : Type} [Preorder ι] {f : ι → TreeComponent n} {z : TreeComponent n}
    (hf : OrderConvergesTo f z) :
    OrderConvergesTo (fun i ↦ finalCoordinateEmbedding n (f i))
      (finalCoordinateEmbedding n z) := by sorry
