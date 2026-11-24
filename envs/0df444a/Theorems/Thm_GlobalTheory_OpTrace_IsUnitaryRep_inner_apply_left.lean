-- Prove2me | Theorems.Thm_GlobalTheory_OpTrace_IsUnitaryRep_inner_apply_left
-- name    : GlobalTheory.OpTrace.IsUnitaryRep.inner_apply_left
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:24:21.245272+00:00
-- url     : https://prove2.me/theorems/f20a4e3c-6f87-410f-a18a-3fe25aff6336
-- title:
--   Is Unitary Rep: inner apply left
-- statement:
--   The Is Unitary Rep construction uses the inner apply left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L359-L366
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L359-L366

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

theorem GlobalTheory.OpTrace.IsUnitaryRep.inner_apply_left {π : G →* (H →L[ℂ] H)} (hπ : IsUnitaryRep π) (g : G)
    (v w : H) : ⟪π g v, w⟫_ℂ = ⟪v, π g⁻¹ w⟫_ℂ := by sorry
