-- Prove2me | Theorems.Thm_Nock_NPR_cpoly_coeff
-- name    : Nock.NPR.cpoly_coeff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:06:20.999809+00:00
-- url     : https://prove2.me/theorems/34301367-7c66-4ad1-89f6-3813283ad237
-- title:
--   NPR: cpoly coeff
-- statement:
--   The NPR construction uses the cpoly coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L60-L66
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L60-L66

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

theorem Nock.NPR.cpoly_coeff (f : ℕ → K) (n j : ℕ) :
    (cpoly f n).coeff j = if j < n then f j else 0 := by sorry
