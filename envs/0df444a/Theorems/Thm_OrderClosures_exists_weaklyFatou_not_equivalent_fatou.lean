-- Prove2me | Theorems.Thm_OrderClosures_exists_weaklyFatou_not_equivalent_fatou
-- name    : OrderClosures.exists_weaklyFatou_not_equivalent_fatou
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:14:27.896805+00:00
-- url     : https://prove2.me/theorems/8c9d3693-f13f-4a18-b6fb-d319f0394b10
-- title:
--   Order Closures: exists weakly Fatou not equivalent fatou
-- statement:
--   Paper Theorem `thm:fremlin-main`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/FinalSpace.lean#L588-L595
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/FinalSpace.lean#L588-L595

module
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_Moderated
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_FinalSpace
set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set Filter Topology
open scoped NNReal Topology
universe u

theorem OrderClosures.exists_weaklyFatou_not_equivalent_fatou :
    ∃ (X : Type) (_ : AddCommGroup X) (_ : Lattice X) (_ : IsOrderedAddMonoid X)
      (_ : VectorLattice X),
      ∃ p : PaperLatticeNorm X, IsCompleteFor p ∧ HasWeakFatouProperty p 2 ∧
        ∀ q : PaperLatticeNorm X, HasFatouProperty q → ¬ EquivalentNorms p q := by sorry
