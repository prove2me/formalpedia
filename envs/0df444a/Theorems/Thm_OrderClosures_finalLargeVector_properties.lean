-- Prove2me | Theorems.Thm_OrderClosures_finalLargeVector_properties
-- name    : OrderClosures.finalLargeVector_properties
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:06:32.524034+00:00
-- url     : https://prove2.me/theorems/8f357dee-f9db-4ddc-a6a7-b79a78faa784
-- title:
--   Order Closures: final Large Vector properties
-- statement:
--   Paper Proposition `prop:zn`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/FinalSpace.lean#L525-L537
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/FinalSpace.lean#L525-L537

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

theorem OrderClosures.finalLargeVector_properties (n : ℕ) :
    finalLargeVector n ∈ iteratedOrderAdherence (unitBallFor finalLatticeNorm) n ∧
      finalLatticeNorm (finalLargeVector n) = (2 : ℝ) ^ n := by sorry
