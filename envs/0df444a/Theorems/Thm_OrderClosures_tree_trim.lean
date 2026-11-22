-- Prove2me | Theorems.Thm_OrderClosures_tree_trim
-- name    : OrderClosures.tree_trim
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:05:48.272167+00:00
-- url     : https://prove2.me/theorems/5b72bed7-3fd7-49f6-966f-c93854e611b1
-- title:
--   Order Closures: tree trim
-- statement:
--   Paper Lemma `lem:trim`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/Bands.lean#L478-L679
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/Bands.lean#L478-L679

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

theorem OrderClosures.tree_trim
    (n : ℕ) (x : ℕ → TreeComponent n) (w : ℕ → TreeCoefficients n)
    {ε : ℝ} (hε : 0 < ε)
    (hw : ∀ m, 0 ≤ w m)
    (hdom : ∀ m, (x m).1 ≤ treeOperator n (w m))
    (hrho : ∀ m, treeRho n (w m) < 1 + ε / 4)
    (hsharp : ∀ B : TreeBandIndex n, ∃ l : ℝ,
      Tendsto (fun m ↦ treeRho n (treeBandProjection n B (w m)))
        atTop (nhds l)) :
    ∃ w' : ℕ → TreeCoefficients n,
      (∀ m, 0 ≤ w' m ∧ (x m).1 ≤ treeOperator n (w' m) ∧
        treeRho n (w' m) < 1 + ε / 2) ∧
      (recurrentBands n w').Finite := by sorry
