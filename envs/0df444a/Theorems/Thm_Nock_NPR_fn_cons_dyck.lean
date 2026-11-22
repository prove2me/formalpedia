-- Prove2me | Theorems.Thm_Nock_NPR_fn_cons_dyck
-- name    : Nock.NPR.fn_cons_dyck
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:10:04.036588+00:00
-- url     : https://prove2.me/theorems/4f11b4fb-f656-4e1c-b813-9574654f617f
-- title:
--   NPR: fn cons dyck
-- statement:
--   `fn₃` (Dyck fingerprint) composes under `cons` with the delimiter power made explicit
--       (evaluation of the corrected `Phi3_cons`):
--       `fn₃(cons(l,r)) = x·fn₃(l) + x^{2λL−1} + x^{2λL}·fn₃(r)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L341-L346
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L341-L346

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

theorem Nock.NPR.fn_cons_dyck (l r : Noun) (x : K) :
    (fn (Noun.cell l r) x).2.2
      = x * (fn l x).2.2 + x ^ (2 * l.leaves - 1)
        + x ^ (2 * l.leaves) * (fn r x).2.2 := by sorry
