-- Prove2me | Theorems.Thm_Nock_NPR_one_sub_one_sub_pow_le
-- name    : Nock.NPR.one_sub_one_sub_pow_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:30:58.208802+00:00
-- url     : https://prove2.me/theorems/a3143e6d-e588-4734-8066-ded699f83aeb
-- title:
--   NPR: one sub one sub pow le
-- statement:
--   **Bernoulli's inequality (the paper's `1 − (1−ε)^m < ε·m` step, main.tex:1200/2361).**
--       For any `ε ≤ 2` and `m : ℕ`, `1 − (1−ε)^m ≤ m·ε`.  This is the pure real inequality
--       relating the paper's two collision-error expressions: the tight
--       `1 − (1−ε)^{k(k−1)/2}` and the union bound `ε·k(k−1)/2` (`m = k(k−1)/2`).
--
--       NOTE: this lemma establishes only the *arithmetic* relation `tight ≤ union`.  It does
--       NOT (and cannot, in this shared-randomness model) establish that the collision
--       probability is bounded by the tight expression — see the ⚠ note on
--       `collision_table_prob_le`.  It is exactly what shows the union bound we DO prove is the
--       weaker (larger) of the paper's two stated bounds, faithfully reproducing the paper's
--       `<` chain.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L692-L698
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L692-L698

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

theorem Nock.NPR.one_sub_one_sub_pow_le (ε : ℚ) (hε : ε ≤ 2) (m : ℕ) :
    1 - (1 - ε) ^ m ≤ (m : ℚ) * ε := by sorry
