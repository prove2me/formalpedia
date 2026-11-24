-- Prove2me | Theorems.Thm_GlobalTheory_OpTrace_IsUnitaryRep_inner_repOp
-- name    : GlobalTheory.OpTrace.IsUnitaryRep.inner_repOp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:15:20.4463+00:00
-- url     : https://prove2.me/theorems/c0d702fc-bfb2-41ab-aed2-504557b88a02
-- title:
--   Is Unitary Rep: inner rep Op
-- statement:
--   The Is Unitary Rep construction uses the inner rep Op property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L421-L425
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L421-L425

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

theorem GlobalTheory.OpTrace.IsUnitaryRep.inner_repOp (hπ : IsUnitaryRep π) (hf : Continuous f)
    (hc : HasCompactSupport f) (w v : H) :
    ⟪w, repOp π μ f v⟫_ℂ = ∫ g, f g * ⟪w, π g v⟫_ℂ ∂μ := by sorry
