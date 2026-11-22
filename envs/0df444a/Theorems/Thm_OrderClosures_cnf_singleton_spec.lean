-- Prove2me | Theorems.Thm_OrderClosures_cnf_singleton_spec
-- name    : OrderClosures.cnf_singleton_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:00:39.055138+00:00
-- url     : https://prove2.me/theorems/9553e810-95da-4021-9078-8743d51fd1c1
-- title:
--   Order Closures: cnf singleton spec
-- statement:
--   Gives the canonical CNF description of a singleton omega monomial; used
--   to translate singleton-chain inequalities into exponent inequalities.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/OrdinalSpace.lean#L264-L283
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/OrdinalSpace.lean#L264-L283

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_CNFOrder
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_OrdinalSpace
set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set
universe u v

theorem OrderClosures.cnf_singleton_spec
    {q γ d : Ordinal.{u}}
    (hq : Ordinal.CNF Ordinal.omega0 q = [(γ, d)]) :
    q = Ordinal.omega0 ^ γ * d ∧ 0 < d ∧ d < Ordinal.omega0 ∧
      Ordinal.log Ordinal.omega0 q = γ := by sorry
