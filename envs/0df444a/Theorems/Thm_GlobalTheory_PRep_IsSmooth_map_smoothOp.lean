-- Prove2me | Theorems.Thm_GlobalTheory_PRep_IsSmooth_map_smoothOp
-- name    : GlobalTheory.PRep.IsSmooth.map_smoothOp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:28:21.98016+00:00
-- url     : https://prove2.me/theorems/1bcd0ba7-6de3-4e2a-8272-37dbbcb5d76d
-- title:
--   Is Smooth: map smooth Op
-- statement:
--   The Is Smooth construction uses the map smooth Op property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L740-L744
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L740-L744

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

theorem GlobalTheory.PRep.IsSmooth.map_smoothOp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (hρ : IsSmooth ρ) (hf : IsLocallyConstant f) (hc : HasCompactSupport f)
    (l : V →ₗ[ℂ] E) (v : V) : l (smoothOp ρ μ f v) = ∫ g, f g • l (ρ g v) ∂μ := by sorry
