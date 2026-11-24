-- Prove2me | Theorems.Thm_GlobalTheory_aestronglyMeasurable_fderiv_apply_of_param
-- name    : GlobalTheory.aestronglyMeasurable_fderiv_apply_of_param
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:05:48.193438+00:00
-- url     : https://prove2.me/theorems/3663c4ed-773f-4ff0-a911-76c1d177e082
-- title:
--   Global Theory: aestrongly Measurable fderiv apply of param
-- statement:
--   The Global Theory construction uses the aestrongly Measurable fderiv apply of param property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FderivIntegralApplyOfHolomorphicOfDominated.lean#L12-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FderivIntegralApplyOfHolomorphicOfDominated.lean#L12-L36

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

theorem GlobalTheory.aestronglyMeasurable_fderiv_apply_of_param {F : T → E → V} {x₀ : E}
    (hmeas : ∀ᶠ y in 𝓝 x₀, AEStronglyMeasurable (fun t => F t y) μ)
    (hdiff : ∀ᵐ t ∂μ, DifferentiableAt ℂ (F t) x₀) (v : E) :
    AEStronglyMeasurable (fun t => fderiv ℂ (F t) x₀ v) μ := by sorry
