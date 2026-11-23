-- Prove2me | Theorems.Thm_GlobalTheory_OpTrace_IsUnitaryRep_isRepOp
-- name    : GlobalTheory.OpTrace.IsUnitaryRep.isRepOp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:27:09.085198+00:00
-- url     : https://prove2.me/theorems/06c1672e-fa24-4ef2-b5aa-afb087089109
-- title:
--   Is Unitary Rep: is Rep Op
-- statement:
--   The Is Unitary Rep construction uses the is Rep Op property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L409-L413
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L409-L413

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
omit [CompleteSpace H]

theorem GlobalTheory.OpTrace.IsUnitaryRep.isRepOp (hπ : IsUnitaryRep π) (hf : Continuous f) (hc : HasCompactSupport f) :
    IsRepOp π μ f (repOp π μ f) := by sorry
