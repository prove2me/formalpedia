-- Prove2me | Theorems.Thm_GlobalTheory_PRep_IsSmooth_isLocallyConstant_orbit
-- name    : GlobalTheory.PRep.IsSmooth.isLocallyConstant_orbit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:40.809055+00:00
-- url     : https://prove2.me/theorems/ef8ca688-852c-414c-8afd-83ac637b1fca
-- title:
--   Is Smooth: is Locally Constant orbit
-- statement:
--   The Is Smooth construction uses the is Locally Constant orbit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L662-L668
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L662-L668

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

theorem GlobalTheory.PRep.IsSmooth.isLocallyConstant_orbit [ContinuousMul G] {ρ : Representation ℂ G V}
    (hρ : IsSmooth ρ) (v : V) : IsLocallyConstant fun g => ρ g v := by sorry
