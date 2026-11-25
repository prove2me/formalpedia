-- Prove2me | Theorems.Thm_GlobalTheory_StableSubset_eight_le_sum_wt
-- name    : GlobalTheory.StableSubset.eight_le_sum_wt
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T02:52:31.686392+00:00
-- url     : https://prove2.me/theorems/85b7e360-8f66-4bf4-be7e-a5a25a72c480
-- title:
--   Stable Subset: eight le sum wt
-- statement:
--   The Stable Subset construction uses the eight le sum wt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/CardPermExistsStableSubsetLe.lean#L99-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/CardPermExistsStableSubsetLe.lean#L99-L132

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FactorialLeTwoMulCardPermWithFixedPointStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardPermExistsStableSubsetLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
open GlobalTheory GlobalTheory.StableSubset
open Finset Equiv

theorem GlobalTheory.StableSubset.eight_le_sum_wt {N a : ℕ} (σ : Perm (Fin N)) (A : Finset (Fin N)) (hA : A.card = a)
    (h : A.map σ.toEmbedding = A) : 8 ≤ ∑ B ∈ powersetCard a (univ : Finset (Fin N)), wt B σ := by sorry
