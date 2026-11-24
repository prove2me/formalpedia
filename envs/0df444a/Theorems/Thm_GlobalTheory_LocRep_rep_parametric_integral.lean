-- Prove2me | Theorems.Thm_GlobalTheory_LocRep_rep_parametric_integral
-- name    : GlobalTheory.LocRep.rep_parametric_integral
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:13:57.480875+00:00
-- url     : https://prove2.me/theorems/73302ca7-348c-4b57-8c0a-9493fb1015b0
-- title:
--   Loc Rep: rep parametric integral
-- statement:
--   The Loc Rep construction uses the rep parametric integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RepresentativeParametricIntegralContinuousFamily.lean#L9-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RepresentativeParametricIntegralContinuousFamily.lean#L9-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocallyIntegrableRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RepresentativeParametricIntegralContinuousFamily
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ContDiff
open GlobalTheory GlobalTheory.LocRep

theorem GlobalTheory.LocRep.rep_parametric_integral : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (ι : K → G → ℂ), (∀ C, IsCompact C → ∃ M : ℝ, ∀ v, IntegrableOn (ι v) C μ ∧ ∫ x in C, ‖ι v x‖ ∂μ ≤ M * ‖v‖) → (∀ (a : ℂ) v w, ι (a • v + w) =ᵐ[μ] fun x => a * ι v x + ι w x) → ∀ (T : Type) [TopologicalSpace T] [SecondCountableTopology T] [T2Space T] [MeasurableSpace T] [BorelSpace T] (ν : Measure T) [IsLocallyFiniteMeasure ν] (Q : Set T) (w : T → K) (φ : T → G → ℂ), IsCompact Q → Continuous w → Continuous (Function.uncurry φ) → (∀ t, ι (w t) =ᵐ[μ] φ t) → (Continuous fun x => ∫ t in Q, φ t x ∂ν) ∧ ι (∫ t in Q, w t ∂ν) =ᵐ[μ] fun x => ∫ t in Q, φ t x ∂ν := by sorry
