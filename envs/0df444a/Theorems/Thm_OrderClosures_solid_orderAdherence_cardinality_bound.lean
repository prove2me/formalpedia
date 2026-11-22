-- Prove2me | Theorems.Thm_OrderClosures_solid_orderAdherence_cardinality_bound
-- name    : OrderClosures.solid_orderAdherence_cardinality_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:08:15.67549+00:00
-- url     : https://prove2.me/theorems/6781486a-ea50-4af5-a590-11bda4bba9bd
-- title:
--   Order Closures: solid order Adherence cardinality bound
-- statement:
--   Paper Proposition `prop:cardinalitybound`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/Counterexample.lean#L417-L523
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/Counterexample.lean#L417-L523

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

theorem OrderClosures.solid_orderAdherence_cardinality_bound
    {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
     {S : Set X} (hS : LatticeOrderedAddCommGroup.IsSolid S) :
    Cardinal.mk (orderAdherence S) ≤ (2 : Cardinal) ^ Cardinal.mk S := by sorry
