-- Prove2me | Theorems.Thm_GlobalTheory_differentiableOn_setIntegral_of_holomorphic_of_continuousOn
-- name    : GlobalTheory.differentiableOn_setIntegral_of_holomorphic_of_continuousOn
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:22:57.485038+00:00
-- url     : https://prove2.me/theorems/de1c25af-8f4f-4842-98b6-f37184b8c18b
-- title:
--   Global Theory: differentiable On set Integral of holomorphic of continuous On
-- statement:
--   The Global Theory construction uses the differentiable On set Integral of holomorphic of continuous On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FderivIntegralApplyOfHolomorphicOfDominated.lean#L111-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FderivIntegralApplyOfHolomorphicOfDominated.lean#L111-L131

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

theorem GlobalTheory.differentiableOn_setIntegral_of_holomorphic_of_continuousOn [TopologicalSpace T]
    [OpensMeasurableSpace T] {F : T → E → V} {U : Set E} (hU : IsOpen U) {S K : Set T}
    (hK : IsCompact K) (hSK : S ⊆ K) (hS : MeasurableSet S) (hfin : μ S ≠ ⊤)
    (hcont : ContinuousOn (Function.uncurry F) (K ×ˢ U))
    (hdiff : ∀ t ∈ S, DifferentiableOn ℂ (F t) U) :
    DifferentiableOn ℂ (fun y => ∫ t in S, F t y ∂μ) U ∧
      ∀ x ∈ U, IntegrableOn (fun t => F t x) S μ ∧
        IntegrableOn (fun t => fderiv ℂ (F t) x) S μ ∧
        HasFDerivAt (fun y => ∫ t in S, F t y ∂μ) (∫ t in S, fderiv ℂ (F t) x ∂μ) x := by sorry
