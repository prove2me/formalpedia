-- Prove2me | Theorems.Thm_OrderClosures_cnf_singleton_exponent_lt_of_isLUB_not_mem
-- name    : OrderClosures.cnf_singleton_exponent_lt_of_isLUB_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:02:07.524931+00:00
-- url     : https://prove2.me/theorems/bd2f4eb5-3d48-40c5-a971-e35f4c8dc121
-- title:
--   Order Closures: cnf singleton exponent lt of is LUB not mem
-- statement:
--   Makes the exponent of a nonattained singleton-chain supremum strictly
--   larger than every member exponent; used at the limit case of the CNF chain.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/OrdinalSpace.lean#L328-L406
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/OrdinalSpace.lean#L328-L406

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_CNFOrder
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_OrdinalSpace
set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set
universe u v

theorem OrderClosures.cnf_singleton_exponent_lt_of_isLUB_not_mem
    (Q : Set (Ordinal.{u})) (a : Ordinal.{u})
    (hsingle : ∀ q ∈ Q, ∃ γ d, Ordinal.CNF Ordinal.omega0 q = [(γ, d)])
    (hlub : IsLUB Q a) (haQ : a ∉ Q)
    {q β c γ d : Ordinal.{u}} (hqQ : q ∈ Q)
    (hq : Ordinal.CNF Ordinal.omega0 q = [(β, c)])
    (ha : Ordinal.CNF Ordinal.omega0 a = [(γ, d)]) : β < γ := by sorry
