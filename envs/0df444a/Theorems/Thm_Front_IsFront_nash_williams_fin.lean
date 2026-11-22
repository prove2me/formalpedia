-- Prove2me | Theorems.Thm_Front_IsFront_nash_williams_fin
-- name    : Front.IsFront.nash_williams_fin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:43:58.084949+00:00
-- url     : https://prove2.me/theorems/6e9ad018-95d5-4e98-a00c-1a7bb11d4735
-- title:
--   Is Front: nash williams fin
-- statement:
--   **Finite-color Nash-Williams.** For a front `F` on `M` and a coloring `c` of finite lists by a
--   finite palette `κ`, there is an infinite subset `M ∘ e ⊆ M` on which `c` is constant over the
--   restricted front.
--
--   Obtained from `IsFront.nash_williams` by induction on the palette with color-blurring: split off one
--   color as a subset `S`, apply the base theorem, and recurse into the smaller palette on the
--   disjoint side (a front via `shrink_isFront`), composing restrictions with `shrink_shrink`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Front/NashWilliams.lean#L273-L279
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Front/NashWilliams.lean#L273-L279

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

theorem Front.IsFront.nash_williams_fin (hF : IsFront F M) {κ : Type*} [Finite κ]
    (c : List ℕ → κ) :
    ∃ e : ℕ → ℕ, StrictMono e ∧ ∃ col : κ,
      ∀ s ∈ shrink F (M ∘ e), c s = col := by sorry
