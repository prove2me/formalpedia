-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_two_mul_traceNorm_comp_le_of_hilbertSchmidt
-- name    : GroundTheory.Automorphic.two_mul_traceNorm_comp_le_of_hilbertSchmidt
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:11:30.849808+00:00
-- url     : https://prove2.me/theorems/3f3bcb27-23db-4c52-a321-2479664bba7e
-- title:
--   Automorphic: two mul trace Norm comp le of hilbert Schmidt
-- statement:
--   The Automorphic construction uses the two mul trace Norm comp le of hilbert Schmidt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceFormulaSpectral.lean#L18-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceFormulaSpectral.lean#L18-L36

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

theorem GroundTheory.Automorphic.two_mul_traceNorm_comp_le_of_hilbertSchmidt (A : K →L[ℂ] H) (B : H →L[ℂ] K) :
    2 * traceNorm (A.comp B) ≤ hsNormSq A + hsNormSq B := by sorry
