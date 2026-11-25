-- Prove2me | Theorems.Thm_GlobalTheory_T_continuousAt_coeff_zero_of_continuousAt_char_series
-- name    : GlobalTheory.T.continuousAt_coeff_zero_of_continuousAt_char_series
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:27:46.539738+00:00
-- url     : https://prove2.me/theorems/822b68b8-356c-4d0a-9a63-788bf63f5440
-- title:
--   T: continuous At coeff zero of continuous At char series
-- statement:
--   The T construction uses the continuous At coeff zero of continuous At char series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousAtCharSeriesCoefZeroStatement.lean#L6-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousAtCharSeriesCoefZeroStatement.lean#L6-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousAtCharSeriesCoefZero
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousAtCharSeriesCoefZeroStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.continuousAt_coeff_zero_of_continuousAt_char_series : ∀ {Y Ξ P : Type} [AddCommGroup Y] [Zero Ξ] [TopologicalSpace P] (e : Ξ → AddChar Y ℂ),
    (∀ a y, ‖e a y‖ = 1) → (∀ y, e 0 y = 1) → (∀ a, a ≠ 0 → ∃ y, e a y ≠ 1) →
    ∀ (c : P → Ξ → ℂ) (p0 : P) (M : Ξ → ℝ), Summable M → (∀ᶠ p in nhds p0, ∀ a, ‖c p a‖ ≤ M a) →
    (∀ y, ContinuousAt (fun p => ∑' a, e a y * c p a) p0) → ContinuousAt (fun p => c p 0) p0 := by sorry
