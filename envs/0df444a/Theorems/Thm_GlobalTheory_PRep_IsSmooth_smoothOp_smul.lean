-- Prove2me | Theorems.Thm_GlobalTheory_PRep_IsSmooth_smoothOp_smul
-- name    : GlobalTheory.PRep.IsSmooth.smoothOp_smul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:33:22.036533+00:00
-- url     : https://prove2.me/theorems/3309e461-8808-4134-bb47-782bf38d1602
-- title:
--   Is Smooth: smooth Op smul
-- statement:
--   The Is Smooth construction uses the smooth Op smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L759-L766
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L759-L766

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

theorem GlobalTheory.PRep.IsSmooth.smoothOp_smul (hρ : IsSmooth ρ) (hf : IsLocallyConstant f)
    (hc : HasCompactSupport f) (c : ℂ) : smoothOp ρ μ (c • f) = c • smoothOp ρ μ f := by sorry
