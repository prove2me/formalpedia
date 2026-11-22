-- Prove2me | Theorems.Thm_Nock_NPR_card_eval_zero_le
-- name    : Nock.NPR.card_eval_zero_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:19:07.909888+00:00
-- url     : https://prove2.me/theorems/6835969f-7907-4ef1-82db-a74012e0fdc0
-- title:
--   NPR: card eval zero le
-- statement:
--   A nonzero polynomial of natDegree `d` vanishes at at most `d` points of `K`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L397-L405
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L397-L405

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
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

theorem Nock.NPR.card_eval_zero_le (q : K[X]) (hq : q ≠ 0) :
    (Finset.univ.filter (fun r : K => q.eval r = 0)).card ≤ q.natDegree := by sorry
