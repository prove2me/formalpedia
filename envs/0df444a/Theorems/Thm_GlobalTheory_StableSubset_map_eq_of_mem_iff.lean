-- Prove2me | Theorems.Thm_GlobalTheory_StableSubset_map_eq_of_mem_iff
-- name    : GlobalTheory.StableSubset.map_eq_of_mem_iff
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T02:01:52.855168+00:00
-- url     : https://prove2.me/theorems/5bae8b91-e0c7-5a32-ad2d-cf7525c37909
-- title:
--   Stable Subset: map eq of mem iff
-- statement:
--   The Stable Subset construction uses the map eq of mem iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/CardPermExistsStableSubsetLe.lean#L15-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/CardPermExistsStableSubsetLe.lean#L15-L21

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

theorem GlobalTheory.StableSubset.map_eq_of_mem_iff {N : ℕ} (σ : Perm (Fin N)) (A : Finset (Fin N))
    (h : ∀ x, x ∈ A → σ x ∈ A) : A.map σ.toEmbedding = A := by sorry
