-- Prove2me | Theorems.Thm_Nock_NPR_NPR_decomp_of_cons
-- name    : Nock.NPR.NPR_decomp_of_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:30:13.687956+00:00
-- url     : https://prove2.me/theorems/ca3087f5-40e2-4f97-a6d9-222982224d49
-- title:
--   NPR: NPR decomp of cons
-- statement:
--   Structural `←` direction of `Lem:NPR_decomp`: if `n` is literally `cons(nL,nR)` then its
--       NPR satisfies the three identities.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L300-L305
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L300-L305

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

theorem Nock.NPR.NPR_decomp_of_cons {n nL nR : Noun} (h : n = Noun.cell nL nR) :
    (Φ (K := K) n).1 = (Φ (K := K) nL).1 * (Φ (K := K) nR).1
    ∧ (Φ (K := K) n).2.1 = (Φ (K := K) nL).2.1 + X ^ nL.leaves * (Φ (K := K) nR).2.1
    ∧ (Φ (K := K) n).2.2 = X * (Φ (K := K) nL).2.2 + X ^ (2 * nL.leaves - 1)
        + X ^ (2 * nL.leaves) * (Φ (K := K) nR).2.2 := by sorry
