-- Prove2me | Theorems.Thm_OrderClosures_separable_weakSequentialNakano_implies_weakNakano
-- name    : OrderClosures.separable_weakSequentialNakano_implies_weakNakano
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:55:58.150136+00:00
-- url     : https://prove2.me/theorems/a13344f4-1dac-4423-b55a-6f5f1bade5b8
-- title:
--   Order Closures: separable weak Sequential Nakano implies weak Nakano
-- statement:
--   Paper Proposition `prop:separable-reduction`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/Reductions.lean#L342-L350
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/Reductions.lean#L342-L350

module
public import Definitions.Def_LeanPool_OrderClosures_OrderAdherence
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_Reductions
set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set Filter Topology
open scoped NNReal Topology
universe u
variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]

theorem OrderClosures.separable_weakSequentialNakano_implies_weakNakano
    {Y : Type u} [NormedAddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y]
    [NormedVectorLattice Y] [TopologicalSpace.SeparableSpace Y]
    {K : ℝ}
    (hseq : IsWeakSequentialNakanoConstant (X := Y) norm K) :
    IsWeakNakanoConstant (X := Y) norm K ∧
      HasWeakFatouProperty (norm : Y → ℝ) K := by sorry
