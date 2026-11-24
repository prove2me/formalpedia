-- Prove2me | Theorems.Thm_GlobalTheory_OpTrace_IsUnitaryRep_isRepOp_of_integrable
-- name    : GlobalTheory.OpTrace.IsUnitaryRep.isRepOp_of_integrable
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:32:29.553508+00:00
-- url     : https://prove2.me/theorems/974a207c-bffe-4e10-ac1f-88ebfca6ef3b
-- title:
--   Is Unitary Rep: is Rep Op of integrable
-- statement:
--   The Is Unitary Rep construction uses the is Rep Op of integrable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L391-L403
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L391-L403

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
omit [CompleteSpace H]

theorem GlobalTheory.OpTrace.IsUnitaryRep.isRepOp_of_integrable (hπ : IsUnitaryRep π) (hf : Integrable f μ)
    (hm : ∀ v, AEStronglyMeasurable (fun g => f g • π g v) μ) : IsRepOp π μ f (repOp π μ f) := by sorry
