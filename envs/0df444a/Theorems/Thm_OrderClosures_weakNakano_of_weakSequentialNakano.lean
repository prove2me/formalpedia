-- Prove2me | Theorems.Thm_OrderClosures_weakNakano_of_weakSequentialNakano
-- name    : OrderClosures.weakNakano_of_weakSequentialNakano
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:56:36.282643+00:00
-- url     : https://prove2.me/theorems/4ee05693-bff0-4c45-aaad-cacdc92424c5
-- title:
--   Order Closures: weak Nakano of weak Sequential Nakano
-- statement:
--   Promotes the sequential weak Nakano estimate to directed sets in a
--   separable normed lattice, by specializing the paper-norm reduction.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/Reductions.lean#L325-L330
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/Reductions.lean#L325-L330

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

theorem OrderClosures.weakNakano_of_weakSequentialNakano
    {Y : Type u} [NormedAddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y]
    [NormedVectorLattice Y] [TopologicalSpace.SeparableSpace Y]
    {K : ℝ} (hseq : IsWeakSequentialNakanoConstant (X := Y) norm K) :
    IsWeakNakanoConstant (X := Y) norm K := by sorry
