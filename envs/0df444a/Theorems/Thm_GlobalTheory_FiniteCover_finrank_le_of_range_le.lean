-- Prove2me | Theorems.Thm_GlobalTheory_FiniteCover_finrank_le_of_range_le
-- name    : GlobalTheory.FiniteCover.finrank_le_of_range_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T13:30:01.76739+00:00
-- url     : https://prove2.me/theorems/db15c658-5dbb-40f4-9441-cdeaf5eb8fbb
-- title:
--   Finite Cover: finrank le of range le
-- statement:
--   The Finite Cover construction uses the finrank le of range le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsCommonMultiple.lean#L7-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsCommonMultiple.lean#L7-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCommonMultiple
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory GlobalTheory.FiniteCover

theorem GlobalTheory.FiniteCover.finrank_le_of_range_le {K P Q E : Type*} [Field K] [AddCommGroup P] [Module K P]
    [AddCommGroup Q] [Module K Q] [AddCommGroup E] [Module K E] [Module.Finite K Q]
    (L : P →ₗ[K] E) (hL : Function.Injective L) (B : Q →ₗ[K] E) (h : ∀ p, ∃ q, B q = L p) :
    finrank K P ≤ finrank K Q := by sorry
