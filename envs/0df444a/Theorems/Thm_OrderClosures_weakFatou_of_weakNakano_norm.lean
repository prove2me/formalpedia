-- Prove2me | Theorems.Thm_OrderClosures_weakFatou_of_weakNakano_norm
-- name    : OrderClosures.weakFatou_of_weakNakano_norm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:56:02.519804+00:00
-- url     : https://prove2.me/theorems/2e69b9b0-6d05-4c69-8e04-794118bae5d2
-- title:
--   Order Closures: weak Fatou of weak Nakano norm
-- statement:
--   Converts the directed weak Nakano estimate into the weak Fatou inequality
--   for an ambient norm, by specializing the paper-norm reduction.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/Reductions.lean#L334-L339
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/Reductions.lean#L334-L339

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

theorem OrderClosures.weakFatou_of_weakNakano_norm
    {Y : Type u} [NormedAddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y]
    [NormedVectorLattice Y] {K : ℝ}
    (hNak : IsWeakNakanoConstant (X := Y) norm K) :
    HasWeakFatouProperty (norm : Y → ℝ) K := by sorry
