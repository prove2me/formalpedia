-- Prove2me | Theorems.Thm_OrderClosures_singletonCNF_step_of_lt
-- name    : OrderClosures.singletonCNF_step_of_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:03:10.852735+00:00
-- url     : https://prove2.me/theorems/99efe3a0-84f0-4ca4-b421-bae7eb2f7a18
-- title:
--   Order Closures: singleton CNF step of lt
-- statement:
--   Turns a strict exponent inequality into a strict CNF extension of
--   singleton monomials; used by `gaoIndex_approximation`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/StageFormula.lean#L270-L289
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/StageFormula.lean#L270-L289

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_OrdinalSpace
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_StageFormula
set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set
universe u v

theorem OrderClosures.singletonCNF_step_of_lt
    {q r δ d ε e : Ordinal.{u}}
    (hq : Ordinal.CNF Ordinal.omega0 q = [(δ, d)])
    (hr : Ordinal.CNF Ordinal.omega0 r = [(ε, e)]) (hqr : q < r) :
    (ε = δ ∧ d < e) ∨ δ < ε := by sorry
