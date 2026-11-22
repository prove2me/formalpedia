-- Prove2me | Theorems.Thm_Front_ramsey_seq_of_nashWilliams
-- name    : Front.ramsey_seq_of_nashWilliams
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:43:57.791063+00:00
-- url     : https://prove2.me/theorems/8c5f5532-812f-4b93-890f-3a710d184486
-- title:
--   Front: ramsey seq of nash Williams
-- statement:
--   **Infinite Ramsey at arbitrary finite arity, via Nash-Williams.** A finite coloring `c` of the
--   size-`k` subsets of `ℕ` admits a strictly monotone `e` and a color `col` such that every size-`k`
--   subset of `range e` has color `col`.
--
--   Obtained by applying `IsFront.nash_williams_fin` to the uniform front `[ℕ]^k` (`powK id k`) with
--   the list-coloring `s ↦ c s.toFinset`, rewriting the restricted front via `shrink_powK`, and
--   bridging the size-`k` `Finset`s with their sorted lists. This matches `infinite_ramsey_seq` and
--   re-derives it from the Nash-Williams theorem.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Front/NashWilliams.lean#L291-L307
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Front/NashWilliams.lean#L291-L307

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

theorem Front.ramsey_seq_of_nashWilliams {κ : Type*} [Finite κ] (k : ℕ) (c : Finset ℕ → κ) :
    ∃ e : ℕ → ℕ, StrictMono e ∧ ∃ col : κ,
      ∀ t : Finset ℕ, ↑t ⊆ Set.range e → t.card = k → c t = col := by sorry
