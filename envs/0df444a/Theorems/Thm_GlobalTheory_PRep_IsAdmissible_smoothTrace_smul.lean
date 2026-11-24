-- Prove2me | Theorems.Thm_GlobalTheory_PRep_IsAdmissible_smoothTrace_smul
-- name    : GlobalTheory.PRep.IsAdmissible.smoothTrace_smul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:40:11.309729+00:00
-- url     : https://prove2.me/theorems/2b0d48f1-016b-48d1-a8bb-06d9b3c2fe39
-- title:
--   Is Admissible: smooth Trace smul
-- statement:
--   The Is Admissible construction uses the smooth Trace smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L806-L812
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L806-L812

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

theorem GlobalTheory.PRep.IsAdmissible.smoothTrace_smul [μ.IsMulLeftInvariant] (hρ : IsAdmissible ρ)
    (hf : IsLocallyConstant f) (hc : HasCompactSupport f) {K : Subgroup G}
    (ho : IsOpen (K : Set G)) (hK : IsCompact (K : Set G)) (c : ℂ) :
    smoothTrace ρ μ (c • f) = c * smoothTrace ρ μ f := by sorry
