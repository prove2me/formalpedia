-- Prove2me | Theorems.Thm_OrderClosures_singletonCNFBelow_isLUB
-- name    : OrderClosures.singletonCNFBelow_isLUB
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:03:01.551414+00:00
-- url     : https://prove2.me/theorems/f2ffe5ed-bf38-46e5-aabc-47dc982a361d
-- title:
--   Order Closures: singleton CNFBelow is LUB
-- statement:
--   Shows that singleton CNF monomials below `γ` have supremum `ω^γ`; used to
--   construct the reverse adherence approximation at limit exponents.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/StageFormula.lean#L225-L266
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/StageFormula.lean#L225-L266

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_OrdinalSpace
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_StageFormula
set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set
universe u v

theorem OrderClosures.singletonCNFBelow_isLUB (γ : Ordinal.{u}) (hγ : γ ≠ 0) :
    IsLUB (singletonCNFBelow γ) (Ordinal.omega0 ^ γ) := by sorry
