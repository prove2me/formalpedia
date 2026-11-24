-- Prove2me | Theorems.Thm_GlobalTheory_continuousAt_charSeries_coef_zero
-- name    : GlobalTheory.continuousAt_charSeries_coef_zero
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:14:41.127083+00:00
-- url     : https://prove2.me/theorems/ea19a2e3-f6d0-48bf-ab0f-8890205661c0
-- title:
--   Global Theory: continuous At char Series coef zero
-- statement:
--   The Global Theory construction uses the continuous At char Series coef zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousAtCharSeriesCoefZero.lean#L178-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousAtCharSeriesCoefZero.lean#L178-L184

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousAtCharSeriesCoefZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology

theorem GlobalTheory.continuousAt_charSeries_coef_zero :
    ∀ {Y Ξ P : Type} [AddCommGroup Y] [Zero Ξ] [TopologicalSpace P] (e : Ξ → AddChar Y ℂ),
    (∀ a y, ‖e a y‖ = 1) → (∀ y, e 0 y = 1) → (∀ a, a ≠ 0 → ∃ y, e a y ≠ 1) →
    ∀ (c : P → Ξ → ℂ) (p0 : P) (M : Ξ → ℝ), Summable M → (∀ᶠ p in nhds p0, ∀ a, ‖c p a‖ ≤ M a) →
    (∀ y, ContinuousAt (fun p => ∑' a, e a y * c p a) p0) → ContinuousAt (fun p => c p 0) p0 := by sorry
