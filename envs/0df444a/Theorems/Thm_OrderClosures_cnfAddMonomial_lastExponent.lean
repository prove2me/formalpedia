-- Prove2me | Theorems.Thm_OrderClosures_cnfAddMonomial_lastExponent
-- name    : OrderClosures.cnfAddMonomial_lastExponent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:01:01.359267+00:00
-- url     : https://prove2.me/theorems/62f166ed-a5b1-4bd1-bde5-c93c007bb9ff
-- title:
--   Order Closures: cnf Add Monomial last Exponent
-- statement:
--   Identifies the final exponent after adding a monomial; used to control
--   subsequent extensions of the constructed CNF list.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/CNFOrder.lean#L211-L237
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/CNFOrder.lean#L211-L237

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

theorem OrderClosures.cnfAddMonomial_lastExponent
    (l : List (Ordinal.{u} × Ordinal.{u})) (γ d : Ordinal.{u}) :
    ((cnfAddMonomial l γ d).getLast?.map Prod.fst).getD 0 = γ := by sorry
