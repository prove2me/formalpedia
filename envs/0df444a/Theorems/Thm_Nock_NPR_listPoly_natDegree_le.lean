-- Prove2me | Theorems.Thm_Nock_NPR_listPoly_natDegree_le
-- name    : Nock.NPR.listPoly_natDegree_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:18:44.479429+00:00
-- url     : https://prove2.me/theorems/f06dae7f-2bca-4d28-b55d-b0c557cb4b16
-- title:
--   NPR: list Poly nat Degree le
-- statement:
--   The NPR construction uses the list Poly nat Degree le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L104-L105
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L104-L105

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

theorem Nock.NPR.listPoly_natDegree_le (l : List K) : (listPoly l).natDegree ≤ l.length - 1 := by sorry
