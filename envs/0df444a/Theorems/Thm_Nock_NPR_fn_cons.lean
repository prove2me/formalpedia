-- Prove2me | Theorems.Thm_Nock_NPR_fn_cons
-- name    : Nock.NPR.fn_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:30:28.750038+00:00
-- url     : https://prove2.me/theorems/d0ec72ec-5eaf-47f4-be8d-d345aa69a274
-- title:
--   NPR: fn cons
-- statement:
--   **Fingerprint `cons` composition (`fn_cons`)** — `fn(cons(l,r); x)` as field arithmetic
--       over the children's fingerprints, with the Dyck delimiter power explicit.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L350-L357
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L350-L357

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

theorem Nock.NPR.fn_cons (l r : Noun) (x : K) :
    fn (Noun.cell l r) x
      = ( (fn l x).1 * (fn r x).1
        , (fn l x).2.1 + (fn l x).1 * (fn r x).2.1
        , x * (fn l x).2.2 + x ^ (2 * l.leaves - 1)
            + x ^ (2 * l.leaves) * (fn r x).2.2 ) := by sorry
