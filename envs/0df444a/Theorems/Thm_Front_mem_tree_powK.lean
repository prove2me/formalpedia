-- Prove2me | Theorems.Thm_Front_mem_tree_powK
-- name    : Front.mem_tree_powK
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:43:27.523289+00:00
-- url     : https://prove2.me/theorems/c914fec1-76ee-43d1-9121-46e84548e48e
-- title:
--   Front: mem tree pow K
-- statement:
--   Membership in the tree of `[M]^k`: increasing lists in `M` of length at most `k`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Front/Rank.lean#L273-L282
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Front/Rank.lean#L273-L282

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

theorem Front.mem_tree_powK (hM : StrictMono M) {k : ℕ} {s : List ℕ} :
    s ∈ tree (powK M k) ↔
      s.Pairwise (· < ·) ∧ (∀ x ∈ s, x ∈ Set.range M) ∧ s.length ≤ k := by sorry
