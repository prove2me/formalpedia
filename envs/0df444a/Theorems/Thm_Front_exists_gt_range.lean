-- Prove2me | Theorems.Thm_Front_exists_gt_range
-- name    : Front.exists_gt_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:43:22.277184+00:00
-- url     : https://prove2.me/theorems/f191229e-f440-4a71-b7c1-9ad6ef06634f
-- title:
--   Front: exists gt range
-- statement:
--   `M` being a strictly monotone enumeration, there is an element of `M` above any bound.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Front/Rank.lean#L190-L191
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Front/Rank.lean#L190-L191

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

theorem Front.exists_gt_range (hM : StrictMono M) (n : ℕ) : ∃ x ∈ Set.range M, n < x := by sorry
