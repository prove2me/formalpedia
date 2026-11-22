-- Prove2me | Theorems.Thm_Nock_NPR_collision_card_le_tight
-- name    : Nock.NPR.collision_card_le_tight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:10:04.479891+00:00
-- url     : https://prove2.me/theorems/b2c73c33-665f-4865-8bd4-d6eb5dcb5a21
-- title:
--   NPR: collision card le tight
-- statement:
--   **lem:ion_univariate_sec (main.tex:1188), cardinality form — tight bound.**
--       For distinct field-nouns of length `≤ Λ`, the fingerprint `fn` collides for at most
--       `2Λ − 1` values of `r ∈ K`.
--
--       "distinct field-nouns" (the paper's `n₁ ≠ n₂` in `𝒩^{λ≤Λ}(𝔽)`, main.tex:1181) is the
--       hypothesis `hne`: the NPR data `(dt, w) = (leafF, dyckBits)` differ.  (Operationally
--       distinct `Noun`s that agree after casting leaves into `K` are the *same* field-noun and
--       genuinely have equal fingerprints, so this is exactly the right premise.)
--
--       Proof = univariate Schwartz–Zippel: at least one of the three difference polynomials
--       `X^{λ₁}−X^{λ₂}`, `F_{d₁}−F_{d₂}`, `F_{w₁}−F_{w₂}` is nonzero of natDegree `≤ 2Λ−1`, and a
--       collision forces `r` to be its root.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L446-L507
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L446-L507

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

theorem Nock.NPR.collision_card_le_tight (Λ : ℕ) (n₁ n₂ : Noun)
    (h₁ : n₁.leaves ≤ Λ) (h₂ : n₂.leaves ≤ Λ)
    (hne : (NPR.leafF (K := K) n₁, NPR.dyckBits (K := K) n₁)
         ≠ (NPR.leafF (K := K) n₂, NPR.dyckBits (K := K) n₂)) :
    (Finset.univ.filter (fun r : K => NPR.fn n₁ r = NPR.fn n₂ r)).card ≤ 2 * Λ - 1 := by sorry
