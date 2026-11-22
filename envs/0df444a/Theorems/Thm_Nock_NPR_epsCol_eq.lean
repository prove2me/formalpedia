-- Prove2me | Theorems.Thm_Nock_NPR_epsCol_eq
-- name    : Nock.NPR.epsCol_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:30:45.661279+00:00
-- url     : https://prove2.me/theorems/0649c4d4-8939-4754-b3a5-8e5194a1d0b1
-- title:
--   NPR: eps Col eq
-- statement:
--   `ε_col` in the paper's real (non-truncated) arithmetic form `2(2Λ−1)/|K|`, valid for
--       `Λ ≥ 1` (main.tex:1204/1192).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L425-L432
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L425-L432

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
omit [Field K] [DecidableEq K]

theorem Nock.NPR.epsCol_eq {Λ : ℕ} (hΛ : 1 ≤ Λ) :
    epsCol (K := K) Λ = 2 * (2 * (Λ : ℚ) - 1) / (Fintype.card K) := by sorry
