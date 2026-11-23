-- Prove2me | Theorems.Thm_GlobalTheory_PRep_IsSmooth_smoothOp_integrand
-- name    : GlobalTheory.PRep.IsSmooth.smoothOp_integrand
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:44:19.422826+00:00
-- url     : https://prove2.me/theorems/43712755-511a-4ff5-a85e-39b31fafccca
-- title:
--   Is Smooth: smooth Op integrand
-- statement:
--   The Is Smooth construction uses the smooth Op integrand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L710-L713
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L710-L713

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
omit [MeasurableSpace G] [BorelSpace G]

theorem GlobalTheory.PRep.IsSmooth.smoothOp_integrand (hρ : IsSmooth ρ) (hf : IsLocallyConstant f)
    (hc : HasCompactSupport f) (v : V) :
    IsLocallyConstant (fun g => f g • ρ g v) ∧ HasCompactSupport fun g => f g • ρ g v := by sorry
