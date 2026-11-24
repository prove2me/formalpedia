-- Prove2me | Theorems.Thm_GlobalTheory_PRep_IsSmooth_map_smoothOp_of_intertwining
-- name    : GlobalTheory.PRep.IsSmooth.map_smoothOp_of_intertwining
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:03:20.588291+00:00
-- url     : https://prove2.me/theorems/1f1863d1-95ea-4640-b822-0cc95999a380
-- title:
--   Is Smooth: map smooth Op of intertwining
-- statement:
--   The Is Smooth construction uses the map smooth Op of intertwining property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L768-L775
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L768-L775

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

theorem GlobalTheory.PRep.IsSmooth.map_smoothOp_of_intertwining {W : Type} [AddCommGroup W] [Module ℂ W]
    {ρ' : Representation ℂ G W} (hρ : IsSmooth ρ) (hρ' : IsSmooth ρ')
    (hf : IsLocallyConstant f) (hc : HasCompactSupport f) (j : V →ₗ[ℂ] W)
    (hj : ∀ g v, j (ρ g v) = ρ' g (j v)) (v : V) :
    j (smoothOp ρ μ f v) = smoothOp ρ' μ f (j v) := by sorry
