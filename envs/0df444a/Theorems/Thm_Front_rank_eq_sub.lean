-- Prove2me | Theorems.Thm_Front_rank_eq_sub
-- name    : Front.rank_eq_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:43:27.274981+00:00
-- url     : https://prove2.me/theorems/bf23b162-b75a-4931-8332-181f725e075c
-- title:
--   Front: rank eq sub
-- statement:
--   **General rank formula.** If, above a fixed node `s0`, every tree node has length `≤ L` and
--   every tree node of length `< L` has a one-step extension in the tree, then the rank of a node `s`
--   above `s0` is `L - s.length`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Front/Rank.lean#L230-L270
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Front/Rank.lean#L230-L270

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

theorem Front.rank_eq_sub (hF : IsFront F M) {s0 : List ℕ} (L : ℕ)
    (hbound : ∀ s, s0 <+: s → s ∈ tree F → s.length ≤ L)
    (hext : ∀ s, s0 <+: s → s ∈ tree F → s.length < L → ∃ x, treeExt F (s ++ [x]) s)
    (s : List ℕ) (hs0 : s0 <+: s) (hs : s ∈ tree F) :
    letI : IsWellFounded (List ℕ) (treeExt F) := ⟨hF.wellFounded_treeExt⟩
    IsWellFounded.rank (treeExt F) s = ((L - s.length : ℕ) : Ordinal) := by sorry
