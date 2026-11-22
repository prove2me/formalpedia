-- Prove2me | Theorems.Thm_OrderClosures_signedPositiveSubsetSuprema_isOrderClosed
-- name    : OrderClosures.signedPositiveSubsetSuprema_isOrderClosed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:01:05.098683+00:00
-- url     : https://prove2.me/theorems/6aa75f5d-2f74-444b-9ab2-47321ee2a70b
-- title:
--   Order Closures: signed Positive Subset Suprema is Order Closed
-- statement:
--   Unnumbered assertion in the proof of `prop:cardinalitybound`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/Counterexample.lean#L395-L414
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/Counterexample.lean#L395-L414

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

theorem OrderClosures.signedPositiveSubsetSuprema_isOrderClosed
    {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
     {S : Set X} (hS : LatticeOrderedAddCommGroup.IsSolid S) :
    IsOrderClosed (signedPositiveSubsetSuprema S) := by sorry
