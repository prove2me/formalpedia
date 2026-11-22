-- Prove2me | Theorems.Thm_OrderClosures_treeOperator_apply_eq_zero_of_outside_support
-- name    : OrderClosures.treeOperator_apply_eq_zero_of_outside_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:06:00.408973+00:00
-- url     : https://prove2.me/theorems/f64be28b-2b08-43aa-b909-b8f9ccbb7955
-- title:
--   Order Closures: tree Operator apply eq zero of outside support
-- statement:
--   Shows that a tree operator vanishes outside the union of cylinders in its
--   support; used by `tree_transient` to eliminate common positive lower bounds.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/Moderated.lean#L89-L102
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/Moderated.lean#L89-L102

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

theorem OrderClosures.treeOperator_apply_eq_zero_of_outside_support
    (n : ℕ) (w : TreeCoefficients n) {α : TreeProduct n}
    (hα : α ∉ finiteCylinderUnion n w.support) :
    treeOperator n w α = 0 := by sorry
