-- Prove2me | Theorems.Thm_GlobalTheory_OpTrace_IsUnitaryRep_comp_repOp
-- name    : GlobalTheory.OpTrace.IsUnitaryRep.comp_repOp
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:37:12.688998+00:00
-- url     : https://prove2.me/theorems/2e3cc281-970a-4bd3-bbce-46b0f17ab336
-- title:
--   Is Unitary Rep: comp rep Op
-- statement:
--   The Is Unitary Rep construction uses the comp rep Op property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L447-L453
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L447-L453

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

theorem GlobalTheory.OpTrace.IsUnitaryRep.comp_repOp {π' : G →* (K →L[ℂ] K)} (hπ : IsUnitaryRep π)
    (hπ' : IsUnitaryRep π') (hf : Continuous f) (hc : HasCompactSupport f) (A : H →L[ℂ] K)
    (hA : ∀ g v, A (π g v) = π' g (A v)) : A ∘L repOp π μ f = repOp π' μ f ∘L A := by sorry
