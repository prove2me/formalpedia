-- Prove2me | Theorems.Thm_Nock_NPR_fn_cons_leaf
-- name    : Nock.NPR.fn_cons_leaf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:18:59.770222+00:00
-- url     : https://prove2.me/theorems/73c5f891-e2d2-4adf-8d1d-2aa6427626c3
-- title:
--   NPR: fn cons leaf
-- statement:
--   `fn₂` (leaf fingerprint) composes affinely under `cons` (evaluation of `Phi2_cons`):
--       `fn₂(cons(l,r)) = fn₂(l) + fn₁(l)·fn₂(r)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L333-L336
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L333-L336

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

theorem Nock.NPR.fn_cons_leaf (l r : Noun) (x : K) :
    (fn (Noun.cell l r) x).2.1 = (fn l x).2.1 + (fn l x).1 * (fn r x).2.1 := by sorry
