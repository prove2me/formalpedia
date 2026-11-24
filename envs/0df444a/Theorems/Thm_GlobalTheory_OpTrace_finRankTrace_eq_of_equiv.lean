-- Prove2me | Theorems.Thm_GlobalTheory_OpTrace_finRankTrace_eq_of_equiv
-- name    : GlobalTheory.OpTrace.finRankTrace_eq_of_equiv
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:37:00.906805+00:00
-- url     : https://prove2.me/theorems/9dffcccc-3682-4485-a266-cfdafc1e1e5f
-- title:
--   Op Trace: fin Rank Trace eq of equiv
-- statement:
--   The Op Trace construction uses the fin Rank Trace eq of equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L560-L578
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L560-L578

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
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem GlobalTheory.OpTrace.finRankTrace_eq_of_equiv {W : Type*} [AddCommGroup W] [Module ℂ W] (e : V ≃ₗ[ℂ] W)
    {T : V →ₗ[ℂ] V} {T' : W →ₗ[ℂ] W} (h : ∀ v, e (T v) = T' (e v))
    [FiniteDimensional ℂ (LinearMap.range T)] :
    FiniteDimensional ℂ (LinearMap.range T') ∧ finRankTrace T' = finRankTrace T := by sorry
