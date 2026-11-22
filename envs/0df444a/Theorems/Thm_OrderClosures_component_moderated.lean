-- Prove2me | Theorems.Thm_OrderClosures_component_moderated
-- name    : OrderClosures.component_moderated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:06:15.922459+00:00
-- url     : https://prove2.me/theorems/6ea473e9-0775-4791-b2bd-db5442d0b557
-- title:
--   Order Closures: component moderated
-- statement:
--   Paper Proposition `prop:moderated`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/Moderated.lean#L234-L430
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/Moderated.lean#L234-L430

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

theorem OrderClosures.component_moderated
    (n : ℕ) (x : ℕ → TreeComponent n) (hxmono : Monotone x)
    (hxpos : ∀ m, 0 ≤ x m) (hxnorm : ∀ m, componentLatticeNorm n (x m) ≤ 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ w : TreeCoefficients n, 0 ≤ w ∧
      (∀ m, (x m).1 ≤ treeOperator n w) ∧ treeRho n w ≤ 2 + ε := by sorry
