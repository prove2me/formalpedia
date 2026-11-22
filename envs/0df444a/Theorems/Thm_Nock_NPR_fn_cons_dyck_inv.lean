-- Prove2me | Theorems.Thm_Nock_NPR_fn_cons_dyck_inv
-- name    : Nock.NPR.fn_cons_dyck_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:30:39.16659+00:00
-- url     : https://prove2.me/theorems/eefafad3-5f2a-4e01-8241-d6dfe6ae1bc7
-- title:
--   NPR: fn cons dyck inv
-- statement:
--   Division form of the Dyck composition, for witness generators that carry a committed
--       `x⁻¹` (`fn₃(cons(l,r)) = x·fn₃(l) + fn₁(l)²·x⁻¹ + fn₁(l)²·fn₃(r)`), valid for `x ≠ 0`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L382-L387
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L382-L387

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

theorem Nock.NPR.fn_cons_dyck_inv (l r : Noun) {x : K} (hx : x ≠ 0) :
    (fn (Noun.cell l r) x).2.2
      = x * (fn l x).2.2 + (fn l x).1 ^ 2 * x⁻¹ + (fn l x).1 ^ 2 * (fn r x).2.2 := by sorry
