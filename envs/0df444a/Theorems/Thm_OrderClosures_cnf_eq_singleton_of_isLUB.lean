-- Prove2me | Theorems.Thm_OrderClosures_cnf_eq_singleton_of_isLUB
-- name    : OrderClosures.cnf_eq_singleton_of_isLUB
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:00:04.087052+00:00
-- url     : https://prove2.me/theorems/c031f9e8-5e5f-4d02-a92d-027cb70b4b11
-- title:
--   Order Closures: cnf eq singleton of is LUB
-- statement:
--   Shows that the least upper bound of a nonempty singleton-monomial chain is
--   itself a singleton monomial; used in the chain-supremum analysis.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/OrdinalSpace.lean#L287-L324
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/OrdinalSpace.lean#L287-L324

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_CNFOrder
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_OrdinalSpace
set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set
universe u v

theorem OrderClosures.cnf_eq_singleton_of_isLUB
    (Q : Set (Ordinal.{u})) (a : Ordinal.{u}) (hQ : Q.Nonempty)
    (hsingle : ∀ q ∈ Q, ∃ γ d, Ordinal.CNF Ordinal.omega0 q = [(γ, d)])
    (hlub : IsLUB Q a) :
    ∃ γ d, Ordinal.CNF Ordinal.omega0 a = [(γ, d)] := by sorry
