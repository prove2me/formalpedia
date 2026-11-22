-- Prove2me | Theorems.Thm_Front_schreier_rank_node
-- name    : Front.schreier_rank_node
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:43:30.776603+00:00
-- url     : https://prove2.me/theorems/aa0d0b67-6525-41e0-9302-ca405d33fcd6
-- title:
--   Front: schreier rank node
-- statement:
--   **Interior of the Schreier front.** A node `s` in the tree with first element `a` has rank
--   `a + 1 - s.length`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Front/Rank.lean#L338-L377
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Front/Rank.lean#L338-L377

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

theorem Front.schreier_rank_node (hM : StrictMono M) {s : List ℕ} {a : ℕ}
    (hsmem : s ∈ tree (schreier M)) (hhead : s.head? = some a) :
    letI : IsWellFounded (List ℕ) (treeExt (schreier M)) :=
      ⟨(isFront_schreier hM).wellFounded_treeExt⟩
    IsWellFounded.rank (treeExt (schreier M)) s = ((a + 1 - s.length : ℕ) : Ordinal) := by sorry
