-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_isTraceClass_comp_of_isHilbertSchmidt
-- name    : GroundTheory.Automorphic.isTraceClass_comp_of_isHilbertSchmidt
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:52:16.846915+00:00
-- url     : https://prove2.me/theorems/e4d2a3a4-e5cd-4ea3-8431-9791db41df90
-- title:
--   Automorphic: is Trace Class comp of is Hilbert Schmidt
-- statement:
--   The Automorphic construction uses the is Trace Class comp of is Hilbert Schmidt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceFormulaSpectral.lean#L38-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceFormulaSpectral.lean#L38-L46

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

theorem GroundTheory.Automorphic.isTraceClass_comp_of_isHilbertSchmidt {A : K →L[ℂ] H} {B : H →L[ℂ] K}
    (hA : IsHilbertSchmidt A) (hB : IsHilbertSchmidt B) : IsTraceClass (A.comp B) := by sorry
