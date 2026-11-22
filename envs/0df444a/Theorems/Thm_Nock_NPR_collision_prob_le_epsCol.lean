-- Prove2me | Theorems.Thm_Nock_NPR_collision_prob_le_epsCol
-- name    : Nock.NPR.collision_prob_le_epsCol
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:30:49.659996+00:00
-- url     : https://prove2.me/theorems/030da377-be3d-4236-8945-e7688e21fb0c
-- title:
--   NPR: collision prob le eps Col
-- statement:
--   **lem:ion_univariate_sec (main.tex:1192), probability form in terms of `ε_col`.**
--       Restatement of `collision_prob_le` against the named constant `epsCol` (main.tex:1204):
--       `Pr_{r∈K}[fn n₁ = fn n₂; n₁ ≠ n₂] ≤ ε_col^{Λ,𝔽}`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L537-L544
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L537-L544

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

theorem Nock.NPR.collision_prob_le_epsCol (Λ : ℕ) (n₁ n₂ : Noun)
    (h₁ : n₁.leaves ≤ Λ) (h₂ : n₂.leaves ≤ Λ)
    (hne : (NPR.leafF (K := K) n₁, NPR.dyckBits (K := K) n₁)
         ≠ (NPR.leafF (K := K) n₂, NPR.dyckBits (K := K) n₂)) :
    ((Finset.univ.filter (fun r : K => NPR.fn n₁ r = NPR.fn n₂ r)).card : ℚ)
        / (Fintype.card K)
      ≤ epsCol (K := K) Λ := by sorry
