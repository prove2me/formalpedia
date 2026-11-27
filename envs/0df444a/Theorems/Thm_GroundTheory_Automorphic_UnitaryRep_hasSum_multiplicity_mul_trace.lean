-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_hasSum_multiplicity_mul_trace
-- name    : GroundTheory.Automorphic.UnitaryRep.hasSum_multiplicity_mul_trace
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:54:06.041992+00:00
-- url     : https://prove2.me/theorems/0d52fda2-1194-5312-b6b1-e904833c4c69
-- title:
--   Unitary Rep: has Sum multiplicity mul trace
-- statement:
--   The Unitary Rep construction uses the has Sum multiplicity mul trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceFormulaSpectral.lean#L181-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceFormulaSpectral.lean#L181-L211

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DiscreteSpectrumAbstract
import Definitions.Def_GroundTheory_AutomorphicForms_TraceClass
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations
import Definitions.Def_GroundTheory_AutomorphicForms_TraceFormulaSpectral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ContinuousLinearMap
open scoped ENNReal InnerProductSpace InnerProduct
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.UnitaryRep
variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
variable (π : UnitaryRep G H) (μ : Measure G) (f : G →₁[μ] ℂ)
variable {J : Type*} {V : J → Submodule ℂ H} [∀ j, CompleteSpace (V j)]
  (hinv : ∀ j, π.IsInvariant (V j))
variable {π μ f}
variable (hsum : IsHilbertSum ℂ (fun j => V j) fun j => (V j).subtypeₗᵢ)
include hsum

theorem GroundTheory.Automorphic.UnitaryRep.hasSum_multiplicity_mul_trace (hT : IsTraceClass (π.integrated μ f))
    (hfin : ∀ j, {k : J | (π.restrict (V k) (hinv k)).IsEquivalent
      (π.restrict (V j) (hinv j))}.Finite) :
    HasSum (fun c : Quotient (restrictSetoid π hinv) => (multiplicity π hinv c : ℂ) *
        trace ((π.restrict (V c.out) (hinv c.out)).integrated μ f))
      (trace (π.integrated μ f)) := by sorry
