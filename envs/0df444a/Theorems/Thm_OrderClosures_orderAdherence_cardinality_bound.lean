-- Prove2me | Theorems.Thm_OrderClosures_orderAdherence_cardinality_bound
-- name    : OrderClosures.orderAdherence_cardinality_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:07:51.370802+00:00
-- url     : https://prove2.me/theorems/4bd0a467-d0ba-49f1-87b5-263764a0fce0
-- title:
--   Order Closures: order Adherence cardinality bound
-- statement:
--   Paper Remark `rem:gao-cardinality`: cardinality of an arbitrary order adherence.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/Counterexample.lean#L77-L151
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/Counterexample.lean#L77-L151

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

theorem OrderClosures.orderAdherence_cardinality_bound
    {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
     (D : Set X) :
    Cardinal.mk (orderAdherence D) ≤
      (2 : Cardinal) ^ ((2 : Cardinal) ^ Cardinal.mk D) := by sorry
