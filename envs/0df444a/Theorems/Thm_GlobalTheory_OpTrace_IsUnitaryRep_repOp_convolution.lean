-- Prove2me | Theorems.Thm_GlobalTheory_OpTrace_IsUnitaryRep_repOp_convolution
-- name    : GlobalTheory.OpTrace.IsUnitaryRep.repOp_convolution
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:14:36.908018+00:00
-- url     : https://prove2.me/theorems/d99cf8bc-ba21-4da0-9e11-8a17e1bbd602
-- title:
--   Is Unitary Rep: rep Op convolution
-- statement:
--   The Is Unitary Rep construction uses the rep Op convolution property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L478-L513
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L478-L513

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

theorem GlobalTheory.OpTrace.IsUnitaryRep.repOp_convolution [IsTopologicalGroup G] [BorelSpace G] [μ.IsMulLeftInvariant]
    (hπ : IsUnitaryRep π) (hf : Continuous f) (hc : HasCompactSupport f)
    (hf' : Continuous f') (hc' : HasCompactSupport f') :
    IsRepOp π μ (fun y => ∫ x, f x * f' (x⁻¹ * y) ∂μ) (repOp π μ f ∘L repOp π μ f') := by sorry
