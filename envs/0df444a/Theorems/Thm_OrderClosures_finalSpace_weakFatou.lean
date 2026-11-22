-- Prove2me | Theorems.Thm_OrderClosures_finalSpace_weakFatou
-- name    : OrderClosures.finalSpace_weakFatou
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:06:22.612597+00:00
-- url     : https://prove2.me/theorems/43aa0fa8-2a16-4230-898e-be8b1ec3b072
-- title:
--   Order Closures: final Space weak Fatou
-- statement:
--   Paper Lemma `lem:c0-weak-fatou`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/FinalSpace.lean#L295-L407
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/FinalSpace.lean#L295-L407

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

theorem OrderClosures.finalSpace_weakFatou :
    IsCompleteFor finalLatticeNorm ∧ HasWeakFatouProperty finalLatticeNorm 2 := by sorry
