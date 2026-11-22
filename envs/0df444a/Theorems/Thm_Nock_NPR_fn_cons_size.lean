-- Prove2me | Theorems.Thm_Nock_NPR_fn_cons_size
-- name    : Nock.NPR.fn_cons_size
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:18:58.082741+00:00
-- url     : https://prove2.me/theorems/277296a8-f9eb-4162-ae99-5faaddba6cbe
-- title:
--   NPR: fn cons size
-- statement:
--   `fn₁` composes multiplicatively under `cons` (evaluation of `Phi1_cons`):
--       `fn₁(cons(l,r)) = fn₁(l)·fn₁(r)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L327-L329
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L327-L329

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

theorem Nock.NPR.fn_cons_size (l r : Noun) (x : K) :
    (fn (Noun.cell l r) x).1 = (fn l x).1 * (fn r x).1 := by sorry
