-- Prove2me | Theorems.Thm_Nock_NPR_listPoly_cons
-- name    : Nock.NPR.listPoly_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:06:22.624216+00:00
-- url     : https://prove2.me/theorems/61998adb-ed68-46a2-8424-b3f96997a010
-- title:
--   NPR: list Poly cons
-- statement:
--   `listPoly (x :: l) = C x + X · listPoly l`: prepending a coefficient shifts by one.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L144-L155
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L144-L155

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

theorem Nock.NPR.listPoly_cons (x : K) (l : List K) :
    listPoly (x :: l) = C x + X * listPoly l := by sorry
