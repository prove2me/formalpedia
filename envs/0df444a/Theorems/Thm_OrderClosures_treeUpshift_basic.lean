-- Prove2me | Theorems.Thm_OrderClosures_treeUpshift_basic
-- name    : OrderClosures.treeUpshift_basic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:05:55.096988+00:00
-- url     : https://prove2.me/theorems/441567b9-9c40-4fbc-8e56-75bdff3cd34b
-- title:
--   Order Closures: tree Upshift basic
-- statement:
--   Paper Lemma `lem:upshift-basic`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/Bands.lean#L309-L341
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/Bands.lean#L309-L341

module
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_TreeNorm
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_Bands
set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set Filter Topology
open scoped NNReal Topology
universe u

theorem OrderClosures.treeUpshift_basic (n : ℕ) (w : TreeCoefficients n) (hw : 0 ≤ w) :
    treeRho n (treeUpshift n w) ≤ 2 * treeRho n w ∧
      treeOperator n w ≤ treeOperator n (treeUpshift n w) := by sorry
