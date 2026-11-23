-- Prove2me | Theorems.Thm_GlobalTheory_OpTrace_integrable_map
-- name    : GlobalTheory.OpTrace.integrable_map
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:41:38.044539+00:00
-- url     : https://prove2.me/theorems/f3262322-8ae8-40ad-bab3-cdd7e577f9af
-- title:
--   Op Trace: integrable map
-- statement:
--   The Op Trace construction uses the integrable map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L717-L719
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L717-L719

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
open GlobalTheory.PRep
variable {G V : Type} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V]
variable [MeasurableSpace G]
variable [IsTopologicalGroup G] [BorelSpace G] {μ : Measure G} [IsFiniteMeasureOnCompacts μ]
  {ρ : Representation ℂ G V} {f f' : G → ℂ}
omit [Module ℂ V]

theorem GlobalTheory.OpTrace.integrable_map {E : Type*} [NormedAddCommGroup E] {F : G → V} (hF : IsLocallyConstant F)
    (hc : HasCompactSupport F) (l : V → E) (hl : l 0 = 0) : Integrable (fun g => l (F g)) μ := by sorry
