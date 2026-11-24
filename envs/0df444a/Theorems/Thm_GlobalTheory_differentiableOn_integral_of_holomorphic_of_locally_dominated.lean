-- Prove2me | Theorems.Thm_GlobalTheory_differentiableOn_integral_of_holomorphic_of_locally_dominated
-- name    : GlobalTheory.differentiableOn_integral_of_holomorphic_of_locally_dominated
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:39.803632+00:00
-- url     : https://prove2.me/theorems/364b4349-57fa-4603-a315-354f93c30608
-- title:
--   Global Theory: differentiable On integral of holomorphic of locally dominated
-- statement:
--   The Global Theory construction uses the differentiable On integral of holomorphic of locally dominated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FderivIntegralApplyOfHolomorphicOfDominated.lean#L92-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FderivIntegralApplyOfHolomorphicOfDominated.lean#L92-L109

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
set_option linter.unusedSectionVars false
variable [CompleteSpace V]

theorem GlobalTheory.differentiableOn_integral_of_holomorphic_of_locally_dominated {F : T → E → V}
    {U : Set E} (hU : IsOpen U)
    (hmeas : ∀ y ∈ U, AEStronglyMeasurable (fun t => F t y) μ)
    (hdiff : ∀ᵐ t ∂μ, DifferentiableOn ℂ (F t) U)
    (hdom : ∀ x ∈ U, ∃ s ∈ 𝓝 x, ∃ bound : T → ℝ, Integrable bound μ ∧
      ∀ᵐ t ∂μ, ∀ y ∈ s, ‖F t y‖ ≤ bound t) :
    DifferentiableOn ℂ (fun y => ∫ t, F t y ∂μ) U ∧
      ∀ x ∈ U, Integrable (fun t => F t x) μ ∧ Integrable (fun t => fderiv ℂ (F t) x) μ ∧
        HasFDerivAt (fun y => ∫ t, F t y ∂μ) (∫ t, fderiv ℂ (F t) x ∂μ) x := by sorry
