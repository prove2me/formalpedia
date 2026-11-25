-- Prove2me | Theorems.Thm_GlobalTheory_OpTrace_IsUnitaryRep_repOp_smul
-- name    : GlobalTheory.OpTrace.IsUnitaryRep.repOp_smul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:14:46.440889+00:00
-- url     : https://prove2.me/theorems/4ad9c60b-7591-4b57-acdc-2a26b1478f7b
-- title:
--   Is Unitary Rep: rep Op smul
-- statement:
--   The Is Unitary Rep construction uses the rep Op smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L440-L445
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L440-L445

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

theorem GlobalTheory.OpTrace.IsUnitaryRep.repOp_smul (hπ : IsUnitaryRep π) (hf : Continuous f)
    (hc : HasCompactSupport f) (c : ℂ) : repOp π μ (c • f) = c • repOp π μ f := by sorry
