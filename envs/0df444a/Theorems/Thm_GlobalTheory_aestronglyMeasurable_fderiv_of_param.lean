-- Prove2me | Theorems.Thm_GlobalTheory_aestronglyMeasurable_fderiv_of_param
-- name    : GlobalTheory.aestronglyMeasurable_fderiv_of_param
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:05:38.818829+00:00
-- url     : https://prove2.me/theorems/983c814e-34c8-4343-9fc1-6bbaa68ce72d
-- title:
--   Global Theory: aestrongly Measurable fderiv of param
-- statement:
--   The Global Theory construction uses the aestrongly Measurable fderiv of param property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FderivIntegralApplyOfHolomorphicOfDominated.lean#L40-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FderivIntegralApplyOfHolomorphicOfDominated.lean#L40-L58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FderivIntegralApplyOfHolomorphicOfDominated
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Metric Set
open scoped Topology Interval
open GlobalTheory
variable {T : Type*} [MeasurableSpace T] {μ : Measure T}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
variable [FiniteDimensional ℂ E]

theorem GlobalTheory.aestronglyMeasurable_fderiv_of_param {F : T → E → V} {x₀ : E}
    (hmeas : ∀ᶠ y in 𝓝 x₀, AEStronglyMeasurable (fun t => F t y) μ)
    (hdiff : ∀ᵐ t ∂μ, DifferentiableAt ℂ (F t) x₀) :
    AEStronglyMeasurable (fun t => fderiv ℂ (F t) x₀) μ := by sorry
