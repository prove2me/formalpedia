-- Prove2me | Theorems.Thm_GlobalTheory_differentiableOn_intervalIntegral_of_holomorphic_of_continuousOn
-- name    : GlobalTheory.differentiableOn_intervalIntegral_of_holomorphic_of_continuousOn
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:13:02.013805+00:00
-- url     : https://prove2.me/theorems/2bfb9056-61a5-45e2-8a32-64da1d72e9dd
-- title:
--   Global Theory: differentiable On interval Integral of holomorphic of continuous On
-- statement:
--   The Global Theory construction uses the differentiable On interval Integral of holomorphic of continuous On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FderivIntegralApplyOfHolomorphicOfDominated.lean#L144-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FderivIntegralApplyOfHolomorphicOfDominated.lean#L144-L165

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

theorem GlobalTheory.differentiableOn_intervalIntegral_of_holomorphic_of_continuousOn {F : ℝ → E → V}
    {U : Set E} (hU : IsOpen U) {a b : ℝ}
    (hcont : ContinuousOn (Function.uncurry F) ([[a, b]] ×ˢ U))
    (hdiff : ∀ t ∈ [[a, b]], DifferentiableOn ℂ (F t) U) :
    DifferentiableOn ℂ (fun y => ∫ t in a..b, F t y) U ∧
      ∀ x ∈ U, IntervalIntegrable (fun t => F t x) volume a b ∧
        IntervalIntegrable (fun t => fderiv ℂ (F t) x) volume a b ∧
        HasFDerivAt (fun y => ∫ t in a..b, F t y) (∫ t in a..b, fderiv ℂ (F t) x) x := by sorry
