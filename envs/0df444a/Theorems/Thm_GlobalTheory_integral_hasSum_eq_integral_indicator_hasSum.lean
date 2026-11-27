-- Prove2me | Theorems.Thm_GlobalTheory_integral_hasSum_eq_integral_indicator_hasSum
-- name    : GlobalTheory.integral_hasSum_eq_integral_indicator_hasSum
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-27T05:47:10.703276+00:00
-- url     : https://prove2.me/theorems/9eebdb1a-025b-4388-967c-c56b384aaee5
-- title:
--   Global Theory: integral has Sum eq integral indicator has Sum
-- statement:
--   The Global Theory construction uses the integral has Sum eq integral indicator has Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegralHasSumEqIntegralIndicatorHasSum.lean#L6-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegralHasSumEqIntegralIndicatorHasSum.lean#L6-L55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralHasSumEqIntegralIndicatorHasSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory

theorem GlobalTheory.integral_hasSum_eq_integral_indicator_hasSum :
    ∀ {X ι : Type} [MeasurableSpace X] [Countable ι] (μ : Measure X) (k : ι → X → ℂ),
      (∀ i, Integrable (k i) μ) → {i | ∫ x, ‖k i x‖ ∂μ ≠ 0}.Finite →
      ∀ (p : Set ι) (K Kp : X → ℂ), (∀ x, HasSum (fun i => k i x) (K x)) →
      (∀ x, HasSum (fun i => p.indicator (fun i => k i x) i) (Kp x)) →
      (∀ i ∉ p, ∫ x, k i x ∂μ = 0) → ∫ x, K x ∂μ = ∫ x, Kp x ∂μ := by sorry
