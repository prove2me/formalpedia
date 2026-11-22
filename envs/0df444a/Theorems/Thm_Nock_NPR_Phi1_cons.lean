-- Prove2me | Theorems.Thm_Nock_NPR_Phi1_cons
-- name    : Nock.NPR.Phi1_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:18:50.994684+00:00
-- url     : https://prove2.me/theorems/5cf28a80-a085-43e2-9fca-d11a485776b7
-- title:
--   NPR: Phi1 cons
-- statement:
--   **`Lem:NPR_decomp`, Φ₁ (main.tex:1221):** `Φ(cons(l,r))₁ = Φ(l)₁ · Φ(r)₁`,
--       i.e. `X^{|dt|} = X^{λL}·X^{λR}`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L247-L249
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L247-L249

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

theorem Nock.NPR.Phi1_cons (l r : Noun) :
    (Φ (K := K) (Noun.cell l r)).1 = (Φ l).1 * (Φ r).1 := by sorry
