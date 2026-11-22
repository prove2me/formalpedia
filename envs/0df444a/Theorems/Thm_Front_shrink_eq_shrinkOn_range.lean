-- Prove2me | Theorems.Thm_Front_shrink_eq_shrinkOn_range
-- name    : Front.shrink_eq_shrinkOn_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:43:45.785172+00:00
-- url     : https://prove2.me/theorems/df479971-6be7-4fb2-97e7-4f556b364655
-- title:
--   Front: shrink eq shrink On range
-- statement:
--   The Front construction uses the shrink eq shrink On range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Front/Shrink.lean#L53-L54
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Front/Shrink.lean#L53-L54

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

theorem Front.shrink_eq_shrinkOn_range (F : Set (List ℕ)) (N : ℕ → ℕ) :
    shrink F N = shrinkOn F (Set.range N) := by sorry
