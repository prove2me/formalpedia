-- Prove2me | Theorems.Thm_OrderClosures_weakNakano_of_weakSequentialNakano_p
-- name    : OrderClosures.weakNakano_of_weakSequentialNakano_p
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:56:00.421791+00:00
-- url     : https://prove2.me/theorems/17b1bd4f-87d8-4c76-872d-768d7efde3f3
-- title:
--   Order Closures: weak Nakano of weak Sequential Nakano p
-- statement:
--   Extends the separable sequential-to-directed reduction to an arbitrary
--   `PaperLatticeNorm`; used to prove `component_weakFatou`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/Reductions.lean#L199-L254
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/Reductions.lean#L199-L254

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

theorem OrderClosures.weakNakano_of_weakSequentialNakano_p
    {Y : Type u} [NormedAddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y]
    [NormedVectorLattice Y] [TopologicalSpace.SeparableSpace Y]
    (p : PaperLatticeNorm Y) {K : ℝ}
    (hseq : IsWeakSequentialNakanoConstant (X := Y) p K) :
    IsWeakNakanoConstant (X := Y) p K := by sorry
