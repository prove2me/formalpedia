-- Prove2me | Theorems.Thm_GlobalTheory_OpTrace_finite_range
-- name    : GlobalTheory.OpTrace.finite_range
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:58:15.938+00:00
-- url     : https://prove2.me/theorems/d514aea4-585e-418b-b835-db131c358b28
-- title:
--   Op Trace: finite range
-- statement:
--   The Op Trace construction uses the finite range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L599-L607
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L599-L607

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
omit [Module ℂ V]

theorem GlobalTheory.OpTrace.finite_range {F : X → V} (hF : IsLocallyConstant F) (hc : HasCompactSupport F) :
    (Set.range F).Finite := by sorry
