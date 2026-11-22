-- Prove2me | Theorems.Thm_Nock_NPR_listPoly_nil
-- name    : Nock.NPR.listPoly_nil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:59:48.914547+00:00
-- url     : https://prove2.me/theorems/bad30145-c8d1-46eb-a56a-7b2800e20a09
-- title:
--   NPR: list Poly nil
-- statement:
--   The NPR construction uses the list Poly nil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L140-L141
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L140-L141

module
public import Definitions.Def_LeanPool_PureNock_Dyck
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Data.List.GetD
public import Mathlib.Tactic.FieldSimp
public import Definitions.Def_LeanPool_PureNock_NPR
set_option autoImplicit true
@[expose] public section
public section
open Polynomial
open Nock
open Nock.NPR
variable {K : Type*} [Field K]

theorem Nock.NPR.listPoly_nil : listPoly ([] : List K) = 0 := by sorry
