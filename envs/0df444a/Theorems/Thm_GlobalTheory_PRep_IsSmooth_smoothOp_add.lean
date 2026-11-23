-- Prove2me | Theorems.Thm_GlobalTheory_PRep_IsSmooth_smoothOp_add
-- name    : GlobalTheory.PRep.IsSmooth.smoothOp_add
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:33:01.345739+00:00
-- url     : https://prove2.me/theorems/f4cb1555-af48-4477-8df1-240efa20e9b1
-- title:
--   Is Smooth: smooth Op add
-- statement:
--   The Is Smooth construction uses the smooth Op add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L746-L757
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L746-L757

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

theorem GlobalTheory.PRep.IsSmooth.smoothOp_add (hρ : IsSmooth ρ) (hf : IsLocallyConstant f)
    (hc : HasCompactSupport f) (hf' : IsLocallyConstant f') (hc' : HasCompactSupport f') :
    smoothOp ρ μ (f + f') = smoothOp ρ μ f + smoothOp ρ μ f' := by sorry
