-- Prove2me | Theorems.Thm_OrderClosures_cnf_singleton_le_leadingCNFTerm
-- name    : OrderClosures.cnf_singleton_le_leadingCNFTerm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:01:58.414194+00:00
-- url     : https://prove2.me/theorems/c567bcfd-308a-4230-bca0-0d39e45705fb
-- title:
--   Order Closures: cnf singleton le leading CNFTerm
-- statement:
--   Bounds a singleton CNF monomial by the leading term of an ordinal; used
--   to identify possible upper bounds of singleton chains.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/OrdinalSpace.lean#L220-L260
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/OrdinalSpace.lean#L220-L260

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_CNFOrder
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_OrdinalSpace
set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set
universe u v

theorem OrderClosures.cnf_singleton_le_leadingCNFTerm
    {q a γ d : Ordinal.{u}}
    (hq : Ordinal.CNF Ordinal.omega0 q = [(γ, d)]) (hqa : q ≤ a) :
    q ≤ leadingCNFTerm a := by sorry
