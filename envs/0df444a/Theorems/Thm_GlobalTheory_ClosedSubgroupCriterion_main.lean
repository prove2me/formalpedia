-- Prove2me | Theorems.Thm_GlobalTheory_ClosedSubgroupCriterion_main
-- name    : GlobalTheory.ClosedSubgroupCriterion.main
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:58:40.574827+00:00
-- url     : https://prove2.me/theorems/455db643-864f-538d-a284-b8f2abcde106
-- title:
--   Closed Subgroup Criterion: main
-- statement:
--   The Closed Subgroup Criterion construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ImportsMore.lean#L5-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ImportsMore.lean#L5-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ImportsMore
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ClosedSubgroupCriterion

theorem GlobalTheory.ClosedSubgroupCriterion.main : ∀ {n j : ℕ} (a : Fin n → ℤ), Antitone a → (∀ (i : Fin n), a i = (0 : ℤ) ∨ a i = (1 : ℤ)) →
    Finset.card {i : Fin n | a i = (1 : ℤ)} = j → ∀ (i : Fin n), a i = (1 : ℤ) ↔ (↑i : ℕ) < j := by sorry
