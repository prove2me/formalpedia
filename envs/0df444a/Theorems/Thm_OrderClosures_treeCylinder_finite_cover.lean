-- Prove2me | Theorems.Thm_OrderClosures_treeCylinder_finite_cover
-- name    : OrderClosures.treeCylinder_finite_cover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:03:35.283804+00:00
-- url     : https://prove2.me/theorems/0c3edd6b-ba7e-42b0-bcd8-c348da09cfa8
-- title:
--   Order Closures: tree Cylinder finite cover
-- statement:
--   Paper Lemma `lem:finite-cover`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/FiniteTree.lean#L236-L264
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/FiniteTree.lean#L236-L264

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

theorem OrderClosures.treeCylinder_finite_cover
    (n : ℕ) (t : TreeNode n) (F : Finset (TreeNode n))
    (hcover : ∀ α ∈ treeCylinder n t, ∃ u ∈ F, α ∈ treeCylinder n u) :
    ∃ u ∈ F, treeCylinder n t ⊆ treeCylinder n u := by sorry
