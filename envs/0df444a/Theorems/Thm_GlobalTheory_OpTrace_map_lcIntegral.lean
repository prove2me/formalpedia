-- Prove2me | Theorems.Thm_GlobalTheory_OpTrace_map_lcIntegral
-- name    : GlobalTheory.OpTrace.map_lcIntegral
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:41:41.784199+00:00
-- url     : https://prove2.me/theorems/f9c4bdb5-18f0-455a-a89d-4291317138e3
-- title:
--   Op Trace: map lc Integral
-- statement:
--   The Op Trace construction uses the map lc Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L615-L639
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L615-L639

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ContinuousLinearMap
open scoped InnerProductSpace Pointwise
noncomputable section
open GlobalTheory GlobalTheory.OpTrace
variable {X V : Type*} [TopologicalSpace X] [AddCommGroup V] [Module ℂ V]
variable [MeasurableSpace X]
variable [OpensMeasurableSpace X] {μ : Measure X} [IsFiniteMeasureOnCompacts μ]

theorem GlobalTheory.OpTrace.map_lcIntegral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {F : X → V} (hF : IsLocallyConstant F) (hc : HasCompactSupport F) (l : V →ₗ[ℂ] E) :
    l (lcIntegral μ F) = ∫ x, l (F x) ∂μ := by sorry
