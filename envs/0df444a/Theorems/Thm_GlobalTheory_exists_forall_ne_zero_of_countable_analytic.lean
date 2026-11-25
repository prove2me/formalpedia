-- Prove2me | Theorems.Thm_GlobalTheory_exists_forall_ne_zero_of_countable_analytic
-- name    : GlobalTheory.exists_forall_ne_zero_of_countable_analytic
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:45:08.426531+00:00
-- url     : https://prove2.me/theorems/19e0a662-10e8-4bc8-9d1e-e5bc48fc76f8
-- title:
--   Global Theory: exists forall ne zero of countable analytic
-- statement:
--   The Global Theory construction uses the exists forall ne zero of countable analytic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsForallNeZeroOfCountableAnalytic.lean#L8-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsForallNeZeroOfCountableAnalytic.lean#L8-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsForallNeZeroOfCountableAnalytic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Matrix
open GlobalTheory

theorem GlobalTheory.exists_forall_ne_zero_of_countable_analytic :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (U : Set E),
      IsOpen U → IsPreconnected U → U.Nonempty → ∀ (ι : Type) [Countable ι] (f : ι → E → ℂ),
      (∀ i, AnalyticOnNhd ℂ (f i) U) → (∀ i, ∃ x ∈ U, f i x ≠ 0) →
      ∃ x ∈ U, ∀ i, f i x ≠ 0 := by sorry
