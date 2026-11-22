-- Prove2me | Theorems.Thm_OrderClosures_component_large_iterated_adherence
-- name    : OrderClosures.component_large_iterated_adherence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:06:18.863787+00:00
-- url     : https://prove2.me/theorems/9d64422a-449f-464b-b461-0d1fb61a87fc
-- title:
--   Order Closures: component large iterated adherence
-- statement:
--   Paper Proposition `prop:component`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/FinalSpace.lean#L32-L97
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/FinalSpace.lean#L32-L97

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

theorem OrderClosures.component_large_iterated_adherence (n : ℕ) :
    TopologicalSpace.IsSeparable (Set.univ : Set (TreeComponent n)) ∧
      IsCompleteFor (componentLatticeNorm n) ∧
      HasWeakFatouProperty (componentLatticeNorm n) 2 ∧
      ((2 : ℝ) ^ n • componentRoot n) ∈
        iteratedOrderAdherence (unitBallFor (componentLatticeNorm n)) n ∧
      componentLatticeNorm n ((2 : ℝ) ^ n • componentRoot n) = (2 : ℝ) ^ n := by sorry
