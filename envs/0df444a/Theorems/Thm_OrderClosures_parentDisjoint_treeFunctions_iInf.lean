-- Prove2me | Theorems.Thm_OrderClosures_parentDisjoint_treeFunctions_iInf
-- name    : OrderClosures.parentDisjoint_treeFunctions_iInf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:12:11.816716+00:00
-- url     : https://prove2.me/theorems/91d623e8-b675-4292-ad1b-4f175e0fedb9
-- title:
--   Order Closures: parent Disjoint tree Functions i Inf
-- statement:
--   Paper Lemma `lem:pi-disjoint`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/FiniteTree.lean#L415-L451
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/FiniteTree.lean#L415-L451

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

theorem OrderClosures.parentDisjoint_treeFunctions_iInf
    (n : ℕ) (F : ℕ → Finset (TreeNode n))
    (hF : Pairwise fun i j ↦ ParentDisjoint (F i : Set (TreeNode n)) (F j : Set (TreeNode n))) :
    IsGLB (Set.range fun m ↦ finiteTreeSup n (F m)) 0 := by sorry
