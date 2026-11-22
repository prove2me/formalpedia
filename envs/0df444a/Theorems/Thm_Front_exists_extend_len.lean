-- Prove2me | Theorems.Thm_Front_exists_extend_len
-- name    : Front.exists_extend_len
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:43:23.351624+00:00
-- url     : https://prove2.me/theorems/25a89f09-f9c7-4dd9-87a8-0f36229ee274
-- title:
--   Front: exists extend len
-- statement:
--   Any increasing list in `M` extends to an increasing list in `M` of any prescribed length.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Front/Rank.lean#L201-L225
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Front/Rank.lean#L201-L225

module
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Defs
public import Mathlib.SetTheory.Ordinal.Rank
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Rank
set_option autoImplicit true
@[expose] public section
public section
open Set List Ordinal
universe u
noncomputable section
open Front
variable {F : Set (List ℕ)} {M : ℕ → ℕ}

theorem Front.exists_extend_len (hM : StrictMono M) (L : ℕ) :
    ∀ (s : List ℕ), s.Pairwise (· < ·) → (∀ x ∈ s, x ∈ Set.range M) →
      s.length ≤ L → ∃ t, s <+: t ∧ t.Pairwise (· < ·) ∧
        (∀ x ∈ t, x ∈ Set.range M) ∧ t.length = L := by sorry
