-- Prove2me | Theorems.Thm_OrderClosures_positiveSubsetSuprema_isOrderClosed
-- name    : OrderClosures.positiveSubsetSuprema_isOrderClosed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:00:46.715797+00:00
-- url     : https://prove2.me/theorems/2f49aa8a-137a-4b38-b343-504d6547487d
-- title:
--   Order Closures: positive Subset Suprema is Order Closed
-- statement:
--   Isolates the order-closedness of positive subset suprema so it can be
--   reused for the signed envelope in `signedPositiveSubsetSuprema_isOrderClosed`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/Counterexample.lean#L301-L392
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/Counterexample.lean#L301-L392

module
public import Mathlib.Data.Fintype.Order
public import Definitions.Def_LeanPool_OrderClosures_Solovay
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungCharacterization
public import Mathlib.Order.TransfiniteIteration
public import Mathlib.SetTheory.Ordinal.CantorNormalForm
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_Counterexample
set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set
universe u v

theorem OrderClosures.positiveSubsetSuprema_isOrderClosed
    {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
     {S : Set X} (hS : LatticeOrderedAddCommGroup.IsSolid S) :
    IsOrderClosed (positiveSubsetSuprema S) := by sorry
