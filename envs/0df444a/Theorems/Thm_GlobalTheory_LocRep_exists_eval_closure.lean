-- Prove2me | Theorems.Thm_GlobalTheory_LocRep_exists_eval_closure
-- name    : GlobalTheory.LocRep.exists_eval_closure
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:13:44.171801+00:00
-- url     : https://prove2.me/theorems/47620d46-d4c1-40c1-a09c-0b991c2457de
-- title:
--   Loc Rep: exists eval closure
-- statement:
--   The Loc Rep construction uses the exists eval closure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsEvaluationExtensionClosureRepresentatives.lean#L12-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsEvaluationExtensionClosureRepresentatives.lean#L12-L108

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocallyIntegrableRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsEvaluationExtensionClosureRepresentatives
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ContDiff
open GlobalTheory GlobalTheory.LocRep
open MeasureTheory Filter Topology
open scoped ContDiff

theorem GlobalTheory.LocRep.exists_eval_closure (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (ι : K → G → ℂ)
    (hloc : ∀ C, IsCompact C → ∃ M : ℝ, ∀ v, IntegrableOn (ι v) C μ ∧ ∫ x in C, ‖ι v x‖ ∂μ ≤ M * ‖v‖)
    (hlin : ∀ (a : ℂ) v w, ι (a • v + w) =ᵐ[μ] fun x => a * ι v x + ι w x)
    (A : K →L[ℂ] K) (E : Submodule ℂ K)
    (hE : ∀ v ∈ E, ∃ φ : G → ℂ, Continuous φ ∧ ι (A v) =ᵐ[μ] φ)
    (hB : ∀ B, IsCompact B → ∃ C : ℝ, ∀ v ∈ E, ∀ φ : G → ℂ, Continuous φ → ι (A v) =ᵐ[μ] φ →
      ∀ x ∈ B, ‖φ x‖ ≤ C * ‖v‖) :
    ∃ Λ : G → (K →L[ℂ] ℂ), ∀ v ∈ closure (E : Set K),
      (Continuous fun x => Λ x v) ∧ ι (A v) =ᵐ[μ] fun x => Λ x v := by sorry
