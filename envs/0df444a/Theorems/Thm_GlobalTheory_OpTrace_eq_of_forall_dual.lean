-- Prove2me | Theorems.Thm_GlobalTheory_OpTrace_eq_of_forall_dual
-- name    : GlobalTheory.OpTrace.eq_of_forall_dual
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:27:18.421834+00:00
-- url     : https://prove2.me/theorems/128667be-ac5f-421d-ac71-0b8dc7ac3606
-- title:
--   Op Trace: eq of forall dual
-- statement:
--   The Op Trace construction uses the eq of forall dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L643-L646
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L643-L646

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
variable {X V : Type*} [TopologicalSpace X] [AddCommGroup V] [Module ℂ V]
variable [MeasurableSpace X]
variable [OpensMeasurableSpace X] {μ : Measure X} [IsFiniteMeasureOnCompacts μ]
omit [MeasurableSpace X] [OpensMeasurableSpace X]

theorem GlobalTheory.OpTrace.eq_of_forall_dual {v w : V} (h : ∀ l : V →ₗ[ℂ] ℂ, l v = l w) : v = w := by sorry
