-- Prove2me | Theorems.Thm_Nock_NPR_collision_card_le
-- name    : Nock.NPR.collision_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:19:06.475796+00:00
-- url     : https://prove2.me/theorems/34d8ecbe-5946-4fe3-8ce1-f9712004a9fd
-- title:
--   NPR: collision card le
-- statement:
--   **lem:ion_univariate_sec (main.tex:1188), cardinality form — paper's stated bound.**
--       The collision set has size `≤ 2(2Λ−1)` (the constant printed in the paper; the tight
--       bound `collision_card_le_tight` gives `2Λ−1`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L512-L517
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L512-L517

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

theorem Nock.NPR.collision_card_le (Λ : ℕ) (n₁ n₂ : Noun)
    (h₁ : n₁.leaves ≤ Λ) (h₂ : n₂.leaves ≤ Λ)
    (hne : (NPR.leafF (K := K) n₁, NPR.dyckBits (K := K) n₁)
         ≠ (NPR.leafF (K := K) n₂, NPR.dyckBits (K := K) n₂)) :
    (Finset.univ.filter (fun r : K => NPR.fn n₁ r = NPR.fn n₂ r)).card ≤ 2 * (2 * Λ - 1) := by sorry
