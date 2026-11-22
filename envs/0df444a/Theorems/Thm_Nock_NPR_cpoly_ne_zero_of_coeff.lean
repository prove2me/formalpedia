-- Prove2me | Theorems.Thm_Nock_NPR_cpoly_ne_zero_of_coeff
-- name    : Nock.NPR.cpoly_ne_zero_of_coeff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:18:39.075804+00:00
-- url     : https://prove2.me/theorems/7c45a496-6d46-4a34-b31d-ebfe797844d8
-- title:
--   NPR: cpoly ne zero of coeff
-- statement:
--   The NPR construction uses the cpoly ne zero of coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L83-L91
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L83-L91

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

theorem Nock.NPR.cpoly_ne_zero_of_coeff {f g : ℕ → K} {n j : ℕ} (hj : j < n) (h : f j ≠ g j) :
    cpoly f n - cpoly g n ≠ 0 := by sorry
