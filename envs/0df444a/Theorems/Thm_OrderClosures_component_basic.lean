-- Prove2me | Theorems.Thm_OrderClosures_component_basic
-- name    : OrderClosures.component_basic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:01:08.776285+00:00
-- url     : https://prove2.me/theorems/dbb69fda-f54d-4905-99ce-b43c5cd3f659
-- title:
--   Order Closures: component basic
-- statement:
--   Paper Corollary `cor:Yn-basic`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/TreeNorm.lean#L636-L688
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/TreeNorm.lean#L636-L688

module
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_FiniteTree
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_TreeNorm
set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set Filter Topology
open scoped NNReal Topology
universe u

theorem OrderClosures.component_basic (n : ℕ) :
    TopologicalSpace.IsSeparable (Set.univ : Set (TreeComponent n)) ∧
      IsCompleteFor (componentLatticeNorm n) ∧
      componentLatticeNorm n (componentRoot n) = 1 ∧
      (∀ t : TreeNode n, TreeNode.level t = n →
        componentLatticeNorm n (componentTreeFunction n t) =
          (2 : ℝ) ^ (-(n : ℤ))) := by sorry
