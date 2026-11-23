-- Prove2me | Theorems.Thm_GlobalTheory_OpTrace_mem_fixed
-- name    : GlobalTheory.OpTrace.mem_fixed
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:41:48.329849+00:00
-- url     : https://prove2.me/theorems/e1a0a911-8cc0-4d49-a207-2f2c60642231
-- title:
--   Op Trace: mem fixed
-- statement:
--   The Op Trace construction uses the mem fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L658-L660
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L658-L660

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
omit [TopologicalSpace G]

theorem GlobalTheory.OpTrace.mem_fixed {ρ : Representation ℂ G V} {K : Subgroup G} {v : V} :
    v ∈ fixed ρ K ↔ ∀ k ∈ K, ρ k v = v := by sorry
