-- Prove2me | Theorems.Thm_GlobalTheory_OpTrace_IsUnitaryRep_adjoint_repOp
-- name    : GlobalTheory.OpTrace.IsUnitaryRep.adjoint_repOp
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:37:05.273675+00:00
-- url     : https://prove2.me/theorems/c31d8e7a-6a4f-4fbf-8157-3b62f84f0941
-- title:
--   Is Unitary Rep: adjoint rep Op
-- statement:
--   The Is Unitary Rep construction uses the adjoint rep Op property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L465-L476
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L465-L476

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

theorem GlobalTheory.OpTrace.IsUnitaryRep.adjoint_repOp [IsTopologicalGroup G] [BorelSpace G] [μ.IsInvInvariant]
    (hπ : IsUnitaryRep π) (hf : Continuous f) (hc : HasCompactSupport f) :
    adjoint (repOp π μ f) = repOp π μ fun g => starRingEnd ℂ (f g⁻¹) := by sorry
