-- Prove2me | Theorems.Thm_GlobalTheory_LocRep_exists_continuous_rep_average
-- name    : GlobalTheory.LocRep.exists_continuous_rep_average
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:13:54.288703+00:00
-- url     : https://prove2.me/theorems/ed519f24-79da-44d8-b44f-c9a2d0b55fbe
-- title:
--   Loc Rep: exists continuous rep average
-- statement:
--   The Loc Rep construction uses the exists continuous rep average property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsContinuousRepresentativeAverage.lean#L11-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsContinuousRepresentativeAverage.lean#L11-L87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocallyIntegrableRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsContinuousRepresentativeAverage
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
open MeasureTheory
open scoped ContDiff Pointwise

theorem GlobalTheory.LocRep.exists_continuous_rep_average : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (ι : K → G → ℂ), (∀ C, IsCompact C → ∃ M : ℝ, ∀ v, IntegrableOn (ι v) C μ ∧ ∫ x in C, ‖ι v x‖ ∂μ ≤ M * ‖v‖) → (∀ (a : ℂ) v w, ι (a • v + w) =ᵐ[μ] fun x => a * ι v x + ι w x) → ∀ (ρ : G →* (K →L[ℂ] K)), (∀ g v, ‖ρ g v‖ = ‖v‖) → (∀ v, Continuous fun g => ρ g v) → (∀ g v, ι (ρ g v) =ᵐ[μ] fun x => ι v (x * g)) → ∀ (η : G → ℂ) (v : K), Continuous η → HasCompactSupport η → ∃ φ : G → ℂ, Continuous φ ∧ ι (∫ y, η y • ρ y v ∂μ) =ᵐ[μ] φ := by sorry
