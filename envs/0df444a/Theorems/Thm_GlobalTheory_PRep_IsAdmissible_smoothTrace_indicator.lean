-- Prove2me | Theorems.Thm_GlobalTheory_PRep_IsAdmissible_smoothTrace_indicator
-- name    : GlobalTheory.PRep.IsAdmissible.smoothTrace_indicator
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:40:08.817302+00:00
-- url     : https://prove2.me/theorems/411ff427-6c90-49db-aa39-5e2d8fd0c228
-- title:
--   Is Admissible: smooth Trace indicator
-- statement:
--   The Is Admissible construction uses the smooth Trace indicator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L823-L856
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L823-L856

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

theorem GlobalTheory.PRep.IsAdmissible.smoothTrace_indicator [μ.IsMulLeftInvariant] (hρ : IsAdmissible ρ)
    {K : Subgroup G} (ho : IsOpen (K : Set G)) (hK : IsCompact (K : Set G)) :
    smoothTrace ρ μ ((K : Set G).indicator fun _ => 1) =
      μ.real K * Module.finrank ℂ (fixed ρ K) := by sorry
