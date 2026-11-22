-- Prove2me | Theorems.Thm_Nock_NPR_cpoly_natDegree_le
-- name    : Nock.NPR.cpoly_natDegree_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:18:41.379814+00:00
-- url     : https://prove2.me/theorems/cf2d4063-a545-432a-ba98-5776c4ffc21c
-- title:
--   NPR: cpoly nat Degree le
-- statement:
--   The NPR construction uses the cpoly nat Degree le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L76-L81
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L76-L81

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

theorem Nock.NPR.cpoly_natDegree_le (f : ℕ → K) (n : ℕ) : (cpoly f n).natDegree ≤ n - 1 := by sorry
