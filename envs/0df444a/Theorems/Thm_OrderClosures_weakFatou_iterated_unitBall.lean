-- Prove2me | Theorems.Thm_OrderClosures_weakFatou_iterated_unitBall
-- name    : OrderClosures.weakFatou_iterated_unitBall
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:55:55.835859+00:00
-- url     : https://prove2.me/theorems/d8419539-8a92-405d-8ce0-3f5ff5660a29
-- title:
--   Order Closures: weak Fatou iterated unit Ball
-- statement:
--   Paper Lemma `lem:fatou-order`, part (a).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/Reductions.lean#L83-L141
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/Reductions.lean#L83-L141

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

theorem OrderClosures.weakFatou_iterated_unitBall
    (p : PaperLatticeNorm X) {K : ℝ} (hK : HasWeakFatouProperty p K) :
    ∀ m ≥ 1, iteratedOrderAdherence (unitBallFor p) m ⊆
      scaleSet (K ^ m) (unitBallFor p) := by sorry
