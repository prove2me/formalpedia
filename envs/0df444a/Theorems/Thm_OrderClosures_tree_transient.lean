-- Prove2me | Theorems.Thm_OrderClosures_tree_transient
-- name    : OrderClosures.tree_transient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:06:16.970827+00:00
-- url     : https://prove2.me/theorems/325fc9be-cadb-4831-be6b-1a7f5ec25816
-- title:
--   Order Closures: tree transient
-- statement:
--   Paper Lemma `lem:transient`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/Moderated.lean#L105-L181
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/Moderated.lean#L105-L181

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

theorem OrderClosures.tree_transient
    (n : ℕ) (w : ℕ → TreeCoefficients n) (Λ : Finset (TreeBandIndex n))
    (hnone : none ∈ Λ)
    (hdis : ∀ B ∉ Λ,
      {m | (treeBandProjection n B (w m)).support.Nonempty}.Subsingleton) :
    let v := fun m ↦ w m - finiteBandProjection n Λ (w m)
    (Pairwise fun i j ↦ ParentDisjoint ((v i).support : Set (TreeNode n))
      ((v j).support : Set (TreeNode n))) ∧
    ∀ z : BoundedContinuousFunction (TreeProduct n) ℝ,
      0 ≤ z → (∀ m, z ≤ treeOperator n (v m)) → z = 0 := by sorry
