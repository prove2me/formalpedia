-- Prove2me | Theorems.Thm_OrderClosures_commonLower_le_zero_of_parentDisjoint_subseq
-- name    : OrderClosures.commonLower_le_zero_of_parentDisjoint_subseq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:56:37.649879+00:00
-- url     : https://prove2.me/theorems/6d029811-0ee6-44ba-a05d-c0c1d945da2c
-- title:
--   Order Closures: common Lower le zero of parent Disjoint subseq
-- statement:
--   Forces a common lower bound to be nonpositive when supports have
--   parent-disjoint subsequences; reused in both tree and transient-band lemmas.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/FiniteTree.lean#L322-L412
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/FiniteTree.lean#L322-L412

module
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_Reductions
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_FiniteTree
set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set Filter Topology
open scoped NNReal Topology
universe u

theorem OrderClosures.commonLower_le_zero_of_parentDisjoint_subseq
    (n : ℕ) (F : ℕ → Finset (TreeNode n))
    (hF : Pairwise fun i j ↦ ParentDisjoint (F i : Set (TreeNode n))
      (F j : Set (TreeNode n)))
    (φ : ℕ → ℕ) (hφ : Function.Injective φ)
    (hroot : ∀ m, TreeNode.root n ∉ F (φ m))
    (g : ℕ → BoundedContinuousFunction (TreeProduct n) ℝ)
    (hgzero : ∀ m α, α ∉ finiteCylinderUnion n (F (φ m)) → g (φ m) α = 0)
    {z : BoundedContinuousFunction (TreeProduct n) ℝ}
    (hz : ∀ m, z ≤ g m) : z ≤ 0 := by sorry
