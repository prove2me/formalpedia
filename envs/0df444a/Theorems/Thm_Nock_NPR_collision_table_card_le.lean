-- Prove2me | Theorems.Thm_Nock_NPR_collision_table_card_le
-- name    : Nock.NPR.collision_table_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:19:08.509443+00:00
-- url     : https://prove2.me/theorems/0562c877-f3c6-42d6-84d2-61ff58481986
-- title:
--   NPR: collision table card le
-- statement:
--   **corr:ion_single_security (main.tex:1197), cardinality form.**  For a table of `k = |s|`
--       nouns of length `≤ Λ`, the number of `r ∈ K` for which *some* pair of distinct nouns
--       collides is `≤ k(k−1)·(2Λ−1)`.  (Union bound over ordered distinct index pairs, each
--       contributing `≤ 2Λ−1` by `collision_card_le_tight`.)
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L563-L613
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L563-L613

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

theorem Nock.NPR.collision_table_card_le {ι : Type*} (Λ : ℕ)
    (s : Finset ι) (f : ι → Noun) (hf : ∀ i ∈ s, (f i).leaves ≤ Λ) :
    (Finset.univ.filter (fun r : K => ∃ ij ∈ s.offDiag,
        NPR.fn (f ij.1) r = NPR.fn (f ij.2) r ∧
        (NPR.leafF (K := K) (f ij.1), NPR.dyckBits (K := K) (f ij.1))
          ≠ (NPR.leafF (K := K) (f ij.2), NPR.dyckBits (K := K) (f ij.2)))).card
      ≤ s.card * (s.card - 1) * (2 * Λ - 1) := by sorry
