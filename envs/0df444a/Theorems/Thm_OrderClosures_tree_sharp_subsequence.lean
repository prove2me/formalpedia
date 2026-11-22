-- Prove2me | Theorems.Thm_OrderClosures_tree_sharp_subsequence
-- name    : OrderClosures.tree_sharp_subsequence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:05:42.6568+00:00
-- url     : https://prove2.me/theorems/b079e7da-482a-432b-a91f-f20bd0b7f360
-- title:
--   Order Closures: tree sharp subsequence
-- statement:
--   Paper Lemma `lem:sharp-subsequence`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/Bands.lean#L399-L424
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/Bands.lean#L399-L424

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

theorem OrderClosures.tree_sharp_subsequence
    (n : ℕ) (w : ℕ → TreeCoefficients n) (C : ℝ)
    (hw : ∀ m, treeRho n (w m) ≤ C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ B : TreeBandIndex n,
      ∃ l : ℝ, Tendsto (fun m ↦ treeRho n (treeBandProjection n B (w (φ m))))
        atTop (nhds l) := by sorry
