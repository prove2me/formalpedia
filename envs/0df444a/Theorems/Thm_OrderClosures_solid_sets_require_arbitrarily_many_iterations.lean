-- Prove2me | Theorems.Thm_OrderClosures_solid_sets_require_arbitrarily_many_iterations
-- name    : OrderClosures.solid_sets_require_arbitrarily_many_iterations
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:11:04.482952+00:00
-- url     : https://prove2.me/theorems/da8f7684-c90f-4df9-8807-81b7bd32c21c
-- title:
--   Order Closures: solid sets require arbitrarily many iterations
-- statement:
--   Paper Theorem `thm:solid-iterations`: constructs solid sets requiring any
--   prescribed admissible number of order-adherence iterations.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/Iterations.lean#L625-L640
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/Iterations.lean#L625-L640

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_StageFormula
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_Iterations
set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set
universe u v

theorem OrderClosures.solid_sets_require_arbitrarily_many_iterations
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ) (ξ : Ordinal.{u})
    (hξ : ξ ≤ Cardinal.ord (Order.succ κ)) :
    ∃ (X : Type (u + 1)) (_ : AddCommGroup X) (_ : Lattice X)
      (_ : IsOrderedAddMonoid X) (_ : VectorLattice X),
      ∃ S : Set X, LatticeOrderedAddCommGroup.IsSolid S ∧
        solidGeneratorNumber S = Cardinal.lift.{u + 1, u} κ ∧
          NeedsOrderAdherenceIterations S (Ordinal.lift.{u + 1, u} ξ) := by sorry
