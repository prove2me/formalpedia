-- Prove2me | Theorems.Thm_OrderClosures_cnfExtensionLE_partialOrder_and_subrelation
-- name    : OrderClosures.cnfExtensionLE_partialOrder_and_subrelation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:58:01.280548+00:00
-- url     : https://prove2.me/theorems/5f39907c-722b-49c4-9094-068786e666b6
-- title:
--   Order Closures: cnf Extension LE partial Order and subrelation
-- statement:
--   Property P1 of the ordinal relation in the proof of `thm:solid-iterations`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/CNFOrder.lean#L663-L698
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/CNFOrder.lean#L663-L698

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_Counterexample
public import Mathlib.SetTheory.Ordinal.Principal
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_CNFOrder
set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set
universe u v

theorem OrderClosures.cnfExtensionLE_partialOrder_and_subrelation :
    IsPartialOrder (Ordinal.{u}) cnfExtensionLE ∧
      ∀ {ζ ζ' : Ordinal.{u}}, cnfExtensionLE ζ ζ' → ζ ≤ ζ' := by sorry
