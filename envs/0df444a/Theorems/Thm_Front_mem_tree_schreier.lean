-- Prove2me | Theorems.Thm_Front_mem_tree_schreier
-- name    : Front.mem_tree_schreier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:43:24.246863+00:00
-- url     : https://prove2.me/theorems/f1c2ada7-e580-4961-b9b9-7ae015eaf88a
-- title:
--   Front: mem tree schreier
-- statement:
--   Membership in the tree of the Schreier front.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Front/Rank.lean#L310-L334
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Front/Rank.lean#L310-L334

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

theorem Front.mem_tree_schreier (hM : StrictMono M) {s : List ℕ} :
    s ∈ tree (schreier M) ↔
      s.Pairwise (· < ·) ∧ (∀ x ∈ s, x ∈ Set.range M) ∧
        (∀ a, s.head? = some a → s.length ≤ a + 1) := by sorry
