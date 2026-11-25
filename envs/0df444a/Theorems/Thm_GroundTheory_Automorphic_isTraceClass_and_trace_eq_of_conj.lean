-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_isTraceClass_and_trace_eq_of_conj
-- name    : GroundTheory.Automorphic.isTraceClass_and_trace_eq_of_conj
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:07:44.278394+00:00
-- url     : https://prove2.me/theorems/26d433f8-3099-4a15-a855-d6ce314bb929
-- title:
--   Automorphic: is Trace Class and trace eq of conj
-- statement:
--   The Automorphic construction uses the is Trace Class and trace eq of conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceFormulaSpectral.lean#L48-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceFormulaSpectral.lean#L48-L65

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
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem GroundTheory.Automorphic.isTraceClass_and_trace_eq_of_conj (e : H ≃ₗᵢ[ℂ] K) {T : H →L[ℂ] H} {S : K →L[ℂ] K}
    (hT : IsTraceClass T) (hS : ∀ v, S (e v) = e (T v)) : IsTraceClass S ∧ trace S = trace T := by sorry
