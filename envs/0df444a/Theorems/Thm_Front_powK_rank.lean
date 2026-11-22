-- Prove2me | Theorems.Thm_Front_powK_rank
-- name    : Front.powK_rank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:43:28.43419+00:00
-- url     : https://prove2.me/theorems/18135a4d-7c5f-4e01-978f-1aca2d3e9ea0
-- title:
--   Front: pow K rank
-- statement:
--   **The uniform front `[M]^k` has rank `k`.**
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Front/Rank.lean#L285-L307
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Front/Rank.lean#L285-L307

module
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Defs
public import Mathlib.SetTheory.Ordinal.Rank
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Rank
public import Theorems.Thm_Front_isFront_powK

set_option autoImplicit true
@[expose] public section
public section
open Set List Ordinal
universe u
noncomputable section
open Front
variable {F : Set (List ℕ)} {M : ℕ → ℕ}

theorem Front.powK_rank (hM : StrictMono M) (k : ℕ) : (isFront_powK hM k).rank = (k : Ordinal) := by sorry
