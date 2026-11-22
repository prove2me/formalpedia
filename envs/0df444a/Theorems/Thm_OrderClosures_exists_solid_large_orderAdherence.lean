-- Prove2me | Theorems.Thm_OrderClosures_exists_solid_large_orderAdherence
-- name    : OrderClosures.exists_solid_large_orderAdherence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:08:11.280751+00:00
-- url     : https://prove2.me/theorems/01aac971-55c2-4f5c-aae5-fcf52e239eb1
-- title:
--   Order Closures: exists solid large order Adherence
-- statement:
--   Paper Proposition `prop:solid-large-order-closure`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/Counterexample.lean#L154-L284
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/Counterexample.lean#L154-L284

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

theorem OrderClosures.exists_solid_large_orderAdherence (κ : Cardinal.{u}) :
    ∃ (X : Type u) (_ : AddCommGroup X) (_ : Lattice X) (_ : IsOrderedAddMonoid X)
      (_ : VectorLattice X),
      ∃ S : Set X, LatticeOrderedAddCommGroup.IsSolid S ∧
        solidGeneratorNumber S = Cardinal.aleph0 ∧
        κ ≤ solidGeneratorNumber (orderAdherence S) := by sorry
