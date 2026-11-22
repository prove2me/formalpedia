-- Prove2me | Theorems.Thm_Nock_NPR_hornerEval_eq_listPoly_eval
-- name    : Nock.NPR.hornerEval_eq_listPoly_eval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:19:15.41146+00:00
-- url     : https://prove2.me/theorems/e168161a-55dc-4cae-b7f6-12e264c28ad1
-- title:
--   NPR: horner Eval eq list Poly eval
-- statement:
--   **Horner = polynomial evaluation.**  `hornerEval r l = (listPoly l).eval r`: the computable
--       Horner scheme agrees with evaluating the coefficient polynomial `Σᵢ lᵢ Xⁱ` at `r`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Fingerprint.lean#L40-L45
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Fingerprint.lean#L40-L45

module
public import Definitions.Def_LeanPool_PureNock_NPR
public import Definitions.Def_LeanPool_PureNock_Fingerprint
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.NPR
open Polynomial
variable {K : Type*} [Field K]

theorem Nock.NPR.hornerEval_eq_listPoly_eval (r : K) (l : List K) :
    hornerEval r l = (listPoly l).eval r := by sorry
