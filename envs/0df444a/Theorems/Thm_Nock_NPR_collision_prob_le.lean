-- Prove2me | Theorems.Thm_Nock_NPR_collision_prob_le
-- name    : Nock.NPR.collision_prob_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:19:06.910679+00:00
-- url     : https://prove2.me/theorems/878dc9b4-5c6e-469b-a0ef-7a49be03583e
-- title:
--   NPR: collision prob le
-- statement:
--   **lem:ion_univariate_sec (main.tex:1188), probability form.**  With the counting-measure
--       convention, `Pr_{r∈K}[fn n₁ = fn n₂] ≤ 2(2Λ−1)/|K| = ε(Λ,K)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L521-L532
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L521-L532

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

theorem Nock.NPR.collision_prob_le (Λ : ℕ) (n₁ n₂ : Noun)
    (h₁ : n₁.leaves ≤ Λ) (h₂ : n₂.leaves ≤ Λ)
    (hne : (NPR.leafF (K := K) n₁, NPR.dyckBits (K := K) n₁)
         ≠ (NPR.leafF (K := K) n₂, NPR.dyckBits (K := K) n₂)) :
    ((Finset.univ.filter (fun r : K => NPR.fn n₁ r = NPR.fn n₂ r)).card : ℚ)
        / (Fintype.card K)
      ≤ ((2 * (2 * Λ - 1) : ℕ) : ℚ) / (Fintype.card K) := by sorry
