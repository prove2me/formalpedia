-- Prove2me | Theorems.Thm_OrderClosures_component_weakFatou
-- name    : OrderClosures.component_weakFatou
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:03:04.904925+00:00
-- url     : https://prove2.me/theorems/aee806f9-168f-480c-93e0-85db631d0902
-- title:
--   Order Closures: component weak Fatou
-- statement:
--   Paper Corollary `cor:weak-fatou`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/Moderated.lean#L433-L457
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/Moderated.lean#L433-L457

module
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_Bands
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_Moderated
set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set Filter Topology
open scoped NNReal Topology
universe u

theorem OrderClosures.component_weakFatou (n : ℕ) :
    IsWeakNakanoConstant (componentLatticeNorm n) 2 ∧
      HasWeakFatouProperty (componentLatticeNorm n) 2 := by sorry
