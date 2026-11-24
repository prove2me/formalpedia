-- Prove2me | Theorems.Thm_GlobalTheory_PRep_IsSmooth_smoothOp_mem_fixed
-- name    : GlobalTheory.PRep.IsSmooth.smoothOp_mem_fixed
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:41:52.1388+00:00
-- url     : https://prove2.me/theorems/30686878-a313-4c8b-ae17-1a6a3c9bad91
-- title:
--   Is Smooth: smooth Op mem fixed
-- statement:
--   The Is Smooth construction uses the smooth Op mem fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L777-L782
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L777-L782

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

theorem GlobalTheory.PRep.IsSmooth.smoothOp_mem_fixed [μ.IsMulLeftInvariant] (hρ : IsSmooth ρ)
    (hf : IsLocallyConstant f) (hc : HasCompactSupport f) {K : Subgroup G}
    (hK : ∀ k ∈ K, ∀ g, f (k * g) = f g) (v : V) : smoothOp ρ μ f v ∈ fixed ρ K := by sorry
