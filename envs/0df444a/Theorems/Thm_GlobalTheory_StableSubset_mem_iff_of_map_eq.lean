-- Prove2me | Theorems.Thm_GlobalTheory_StableSubset_mem_iff_of_map_eq
-- name    : GlobalTheory.StableSubset.mem_iff_of_map_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T02:02:52.898546+00:00
-- url     : https://prove2.me/theorems/db080cc5-2a90-445f-922e-f48c4eaa0ab7
-- title:
--   Stable Subset: mem iff of map eq
-- statement:
--   The Stable Subset construction uses the mem iff of map eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/CardPermExistsStableSubsetLe.lean#L10-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/CardPermExistsStableSubsetLe.lean#L10-L13

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

theorem GlobalTheory.StableSubset.mem_iff_of_map_eq {N : ℕ} (σ : Perm (Fin N)) (A : Finset (Fin N))
    (h : A.map σ.toEmbedding = A) (x : Fin N) : σ x ∈ A ↔ x ∈ A := by sorry
