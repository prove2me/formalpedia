-- Prove2me | Theorems.Thm_GlobalTheory_OpTrace_repTrace_charRep
-- name    : GlobalTheory.OpTrace.repTrace_charRep
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:45:42.145793+00:00
-- url     : https://prove2.me/theorems/a3759a3c-7f6f-476f-8c01-7c6333baf099
-- title:
--   Op Trace: rep Trace char Rep
-- statement:
--   The Op Trace construction uses the rep Trace char Rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L515-L524
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L515-L524

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
variable {G : Type*} [Group G] [TopologicalSpace G]
  {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable [MeasurableSpace G]
variable {π : G →* (H →L[ℂ] H)} {μ : Measure G} {f f' : G → ℂ}
variable [OpensMeasurableSpace G] [IsFiniteMeasureOnCompacts μ]

theorem GlobalTheory.OpTrace.repTrace_charRep {χ : G →* Circle} (hχ : Continuous χ) (hf : Continuous f)
    (hc : HasCompactSupport f) :
    HasTrace (repOp (charRep χ) μ f) (∫ g, f g * (χ g : ℂ) ∂μ) := by sorry
