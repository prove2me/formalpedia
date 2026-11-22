-- Prove2me | Theorems.Thm_Nock_NPR_Phi3_cons
-- name    : Nock.NPR.Phi3_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:10:09.464911+00:00
-- url     : https://prove2.me/theorems/51123caf-7f1f-4e2f-88fc-55cb2c61336f
-- title:
--   NPR: Phi3 cons
-- statement:
--   **`Lem:NPR_decomp`, Φ₃ (main.tex:1223), CORRECTED exponents (see the section header):**
--       `Φ(cons(l,r))₃ = X·Φ(l)₃ + X^{2λL−1} + X^{2λL}·Φ(r)₃`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L258-L265
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L258-L265

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

theorem Nock.NPR.Phi3_cons (l r : Noun) :
    (Φ (K := K) (Noun.cell l r)).2.2
      = X * (Φ l).2.2 + X ^ (2 * l.leaves - 1) + X ^ (2 * l.leaves) * (Φ r).2.2 := by sorry
