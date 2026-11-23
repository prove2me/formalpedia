-- Prove2me | Theorems.Thm_GlobalTheory_OpTrace_finRankTrace_eq
-- name    : GlobalTheory.OpTrace.finRankTrace_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:43:42.841198+00:00
-- url     : https://prove2.me/theorems/48f52eb3-367e-47b1-b5e5-1ce321a8f839
-- title:
--   Op Trace: fin Rank Trace eq
-- statement:
--   The Op Trace construction uses the fin Rank Trace eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L535-L540
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L535-L540

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

theorem GlobalTheory.OpTrace.finRankTrace_eq (T : V →ₗ[ℂ] V) (W : Submodule ℂ V) [FiniteDimensional ℂ W]
    (hW : ∀ x, T x ∈ W) :
    finRankTrace T = LinearMap.trace ℂ W (T.restrict fun x _ => hW x) := by sorry
