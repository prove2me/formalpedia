-- Prove2me | Theorems.Thm_Nock_NPR_collision_table_prob_le_epsCol
-- name    : Nock.NPR.collision_table_prob_le_epsCol
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:30:53.775558+00:00
-- url     : https://prove2.me/theorems/a609c44c-139b-479a-8060-8171e9ab5156
-- title:
--   NPR: collision table prob le eps Col
-- statement:
--   **corr:ion_single_security (main.tex:1197), union bound in terms of `ε_col`.**
--       Restatement of `collision_table_prob_le` against the named constant `epsCol`
--       (main.tex:1204): `Pr[∃ colliding pair] ≤ ε_col^{Λ,𝔽} · k(k−1)/2`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L671-L679
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L671-L679

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

theorem Nock.NPR.collision_table_prob_le_epsCol {ι : Type*} (Λ : ℕ)
    (s : Finset ι) (f : ι → Noun) (hf : ∀ i ∈ s, (f i).leaves ≤ Λ) :
    ((Finset.univ.filter (fun r : K => ∃ ij ∈ s.offDiag,
        NPR.fn (f ij.1) r = NPR.fn (f ij.2) r ∧
        (NPR.leafF (K := K) (f ij.1), NPR.dyckBits (K := K) (f ij.1))
          ≠ (NPR.leafF (K := K) (f ij.2), NPR.dyckBits (K := K) (f ij.2)))).card : ℚ)
        / (Fintype.card K)
      ≤ epsCol (K := K) Λ * ((s.card : ℚ) * ((s.card : ℚ) - 1) / 2) := by sorry
