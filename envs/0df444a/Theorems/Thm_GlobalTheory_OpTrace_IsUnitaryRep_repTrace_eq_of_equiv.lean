-- Prove2me | Theorems.Thm_GlobalTheory_OpTrace_IsUnitaryRep_repTrace_eq_of_equiv
-- name    : GlobalTheory.OpTrace.IsUnitaryRep.repTrace_eq_of_equiv
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:14:39.273777+00:00
-- url     : https://prove2.me/theorems/f183c4d7-0a02-5f8d-8464-ed95cbb174e8
-- title:
--   Is Unitary Rep: rep Trace eq of equiv
-- statement:
--   The Is Unitary Rep construction uses the rep Trace eq of equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L455-L463
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L455-L463

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

theorem GlobalTheory.OpTrace.IsUnitaryRep.repTrace_eq_of_equiv {π' : G →* (K →L[ℂ] K)} (hπ : IsUnitaryRep π)
    (hπ' : IsUnitaryRep π') (hf : Continuous f) (hc : HasCompactSupport f) (A : H ≃L[ℂ] K)
    (hA : ∀ g v, A (π g v) = π' g (A v)) (ht : IsTraceClass (repOp π μ f)) :
    IsTraceClass (repOp π' μ f) ∧ repTrace π' μ f = repTrace π μ f := by sorry
