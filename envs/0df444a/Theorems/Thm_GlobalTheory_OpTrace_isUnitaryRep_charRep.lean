-- Prove2me | Theorems.Thm_GlobalTheory_OpTrace_isUnitaryRep_charRep
-- name    : GlobalTheory.OpTrace.isUnitaryRep_charRep
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:03:48.146659+00:00
-- url     : https://prove2.me/theorems/e8b90e1d-33d1-4269-b109-9d87b106223f
-- title:
--   Op Trace: is Unitary Rep char Rep
-- statement:
--   The Op Trace construction uses the is Unitary Rep char Rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L355-L357
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L355-L357

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

theorem GlobalTheory.OpTrace.isUnitaryRep_charRep {χ : G →* Circle} (hχ : Continuous χ) : IsUnitaryRep (charRep χ) := by sorry
