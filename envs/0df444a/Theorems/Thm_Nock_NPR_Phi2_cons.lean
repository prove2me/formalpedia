-- Prove2me | Theorems.Thm_Nock_NPR_Phi2_cons
-- name    : Nock.NPR.Phi2_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:18:52.522822+00:00
-- url     : https://prove2.me/theorems/f91ec531-ecc2-4ae3-a432-1d22142d909c
-- title:
--   NPR: Phi2 cons
-- statement:
--   **`Lem:NPR_decomp`, Φ₂ (main.tex:1222):** `Φ(cons(l,r))₂ = Φ(l)₂ + X^{λL}·Φ(r)₂`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L252-L254
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L252-L254

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

theorem Nock.NPR.Phi2_cons (l r : Noun) :
    (Φ (K := K) (Noun.cell l r)).2.1 = (Φ l).2.1 + X ^ l.leaves * (Φ r).2.1 := by sorry
