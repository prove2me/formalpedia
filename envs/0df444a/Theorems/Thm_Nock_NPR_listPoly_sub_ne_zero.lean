-- Prove2me | Theorems.Thm_Nock_NPR_listPoly_sub_ne_zero
-- name    : Nock.NPR.listPoly_sub_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:18:44.847319+00:00
-- url     : https://prove2.me/theorems/43b77942-173c-4182-9fcb-3c1de54135d3
-- title:
--   NPR: list Poly sub ne zero
-- statement:
--   Two equal-length lists that differ have distinct coefficient polynomials.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L108-L122
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L108-L122

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

theorem Nock.NPR.listPoly_sub_ne_zero {l₁ l₂ : List K} (hlen : l₁.length = l₂.length) (hne : l₁ ≠ l₂) :
    listPoly l₁ - listPoly l₂ ≠ 0 := by sorry
