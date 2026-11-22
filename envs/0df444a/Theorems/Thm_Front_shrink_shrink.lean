-- Prove2me | Theorems.Thm_Front_shrink_shrink
-- name    : Front.shrink_shrink
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:43:37.942401+00:00
-- url     : https://prove2.me/theorems/67948037-db52-42c7-ba10-54cce39f2ca5
-- title:
--   Front: shrink shrink
-- statement:
--   Restricting twice to nested subsets collapses to the inner restriction.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Front/Shrink.lean#L107-L113
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Front/Shrink.lean#L107-L113

module
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Rank
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Shrink
set_option autoImplicit true
@[expose] public section
public section
open Set List
noncomputable section
open Front
variable {F : Set (List ℕ)} {M : ℕ → ℕ}

theorem Front.shrink_shrink {N N' : ℕ → ℕ} (h : Set.range N' ⊆ Set.range N) :
    shrink (shrink F N) N' = shrink F N' := by sorry
