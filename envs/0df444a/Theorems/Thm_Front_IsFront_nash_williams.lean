-- Prove2me | Theorems.Thm_Front_IsFront_nash_williams
-- name    : Front.IsFront.nash_williams
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:44:01.068761+00:00
-- url     : https://prove2.me/theorems/1d45ba68-433d-46b3-8cdc-20e0ef1085a6
-- title:
--   Is Front: nash williams
-- statement:
--   **The Nash-Williams theorem (subset form).** For a front `F` on `M` and any subset `S`, there
--   is an infinite subset `X ⊆ range M` on which the restricted front `shrinkOn F X` (the survey's
--   `F ↾ X`) is entirely inside `S` or entirely outside `S`.
--
--   The carrier is stated as a set `X`; its strictly monotone enumeration `N` (with `Set.range N = X`,
--   so that `shrinkOn F X = shrink F N`) is recovered through `Set.Infinite.exists_strictMono_range`.
--
--   Proved by transfinite recursion on `hF.rank` (the *ray recursion*).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Front/NashWilliams.lean#L227-L233
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Front/NashWilliams.lean#L227-L233

module
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Shrink
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Ray
public import Definitions.Def_LeanPool_NashWilliams_Data_Fintype_Pigeonhole
public import Definitions.Def_LeanPool_NashWilliams_Data_Nat_Nth
public import Mathlib.Data.Finset.Sort
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_NashWilliams
set_option autoImplicit true
@[expose] public section
public section
open Set List
noncomputable section
open Front
variable {F : Set (List ℕ)} {M : ℕ → ℕ}

theorem Front.IsFront.nash_williams (hF : IsFront F M) (S : Set (List ℕ)) :
    ∃ X : Set ℕ, X ⊆ Set.range M ∧ X.Infinite ∧
      (shrinkOn F X ⊆ S ∨ Disjoint (shrinkOn F X) S) := by sorry
