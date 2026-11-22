-- Prove2me | Theorems.Thm_OrderClosures_fatou_iterated_unitBall
-- name    : OrderClosures.fatou_iterated_unitBall
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:55:59.127432+00:00
-- url     : https://prove2.me/theorems/0c2185c3-9d78-41a2-a95b-564e557defbd
-- title:
--   Order Closures: fatou iterated unit Ball
-- statement:
--   Paper Lemma `lem:fatou-order`, part (b).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/Reductions.lean#L144-L176
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/Reductions.lean#L144-L176

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

theorem OrderClosures.fatou_iterated_unitBall
    (p : PaperLatticeNorm X) (hp : HasFatouProperty p) :
    ∀ m ≥ 1, iteratedOrderAdherence (unitBallFor p) m = unitBallFor p := by sorry
