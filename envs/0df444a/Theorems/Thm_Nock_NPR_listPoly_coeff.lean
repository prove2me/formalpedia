-- Prove2me | Theorems.Thm_Nock_NPR_listPoly_coeff
-- name    : Nock.NPR.listPoly_coeff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:18:51.6833+00:00
-- url     : https://prove2.me/theorems/349efc12-49c8-48c1-ba75-5c984b216ef0
-- title:
--   NPR: list Poly coeff
-- statement:
--   The NPR construction uses the list Poly coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L136-L138
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L136-L138

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

theorem Nock.NPR.listPoly_coeff (l : List K) (j : ℕ) :
    (listPoly l).coeff j = if j < l.length then l.getD j 0 else 0 := by sorry
