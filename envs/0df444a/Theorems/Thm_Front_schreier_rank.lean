-- Prove2me | Theorems.Thm_Front_schreier_rank
-- name    : Front.schreier_rank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:43:32.273809+00:00
-- url     : https://prove2.me/theorems/811c7eee-e41b-462e-af51-db22094c4a5d
-- title:
--   Front: schreier rank
-- statement:
--   **The Schreier front has rank `ω`.**
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Front/Rank.lean#L380-L415
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Front/Rank.lean#L380-L415

module
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Defs
public import Mathlib.SetTheory.Ordinal.Rank
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Rank
public import Theorems.Thm_Front_isFront_schreier

set_option autoImplicit true
@[expose] public section
public section
open Set List Ordinal
universe u
noncomputable section
open Front
variable {F : Set (List ℕ)} {M : ℕ → ℕ}

theorem Front.schreier_rank (hM : StrictMono M) : (isFront_schreier hM).rank = ω := by sorry
