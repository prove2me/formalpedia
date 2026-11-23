-- Prove2me | Theorems.Thm_GlobalTheory_OpTrace_IsRepOp_repOp_eq
-- name    : GlobalTheory.OpTrace.IsRepOp.repOp_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:43:56.369216+00:00
-- url     : https://prove2.me/theorems/7c22c70e-60af-48ee-9c13-fa48b2a4aad5
-- title:
--   Is Rep Op: rep Op eq
-- statement:
--   The Is Rep Op construction uses the rep Op eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L384-L387
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L384-L387

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
omit [TopologicalSpace G] [CompleteSpace H]

theorem GlobalTheory.OpTrace.IsRepOp.repOp_eq {T : H →L[ℂ] H} (h : IsRepOp π μ f T) : repOp π μ f = T := by sorry
