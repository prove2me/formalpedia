-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_Equiv_isTraceClass_integrated_and_trace_eq
-- name    : GroundTheory.Automorphic.UnitaryRep.Equiv.isTraceClass_integrated_and_trace_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:56:48.025674+00:00
-- url     : https://prove2.me/theorems/d34da57c-f138-43ac-abae-e91866607f0c
-- title:
--   Equiv: is Trace Class integrated and trace eq
-- statement:
--   The Equiv construction uses the is Trace Class integrated and trace eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceFormulaSpectral.lean#L80-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceFormulaSpectral.lean#L80-L85

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
variable {μ : Measure G} {σ : UnitaryRep G K} {τ : UnitaryRep G L}

theorem GroundTheory.Automorphic.UnitaryRep.Equiv.isTraceClass_integrated_and_trace_eq (e : σ.Equiv τ) (f : G →₁[μ] ℂ)
    (h : IsTraceClass (σ.integrated μ f)) :
    IsTraceClass (τ.integrated μ f) ∧ trace (τ.integrated μ f) = trace (σ.integrated μ f) := by sorry
