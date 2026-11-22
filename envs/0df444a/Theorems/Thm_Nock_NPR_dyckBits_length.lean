-- Prove2me | Theorems.Thm_Nock_NPR_dyckBits_length
-- name    : Nock.NPR.dyckBits_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:09:54.752945+00:00
-- url     : https://prove2.me/theorems/d5a81f7c-a19f-4698-9276-c3286ef62d97
-- title:
--   NPR: dyck Bits length
-- statement:
--   The NPR construction uses the dyck Bits length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L184-L186
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L184-L186

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

theorem Nock.NPR.dyckBits_length (n : Noun) : (dyckBits (K := K) n).length + 2 = 2 * n.leaves := by sorry
