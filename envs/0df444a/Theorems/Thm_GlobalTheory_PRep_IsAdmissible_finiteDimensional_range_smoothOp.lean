-- Prove2me | Theorems.Thm_GlobalTheory_PRep_IsAdmissible_finiteDimensional_range_smoothOp
-- name    : GlobalTheory.PRep.IsAdmissible.finiteDimensional_range_smoothOp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:43:41.853526+00:00
-- url     : https://prove2.me/theorems/7d953e81-7134-42ba-aa01-c6e67ea8bb64
-- title:
--   Is Admissible: finite Dimensional range smooth Op
-- statement:
--   The Is Admissible construction uses the finite Dimensional range smooth Op property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L784-L794
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L784-L794

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

theorem GlobalTheory.PRep.IsAdmissible.finiteDimensional_range_smoothOp [μ.IsMulLeftInvariant] (hρ : IsAdmissible ρ)
    (hf : IsLocallyConstant f) (hc : HasCompactSupport f) {K : Subgroup G}
    (ho : IsOpen (K : Set G)) (hK : IsCompact (K : Set G)) :
    FiniteDimensional ℂ (LinearMap.range (smoothOp ρ μ f)) := by sorry
