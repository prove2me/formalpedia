-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TubeFourier_integrable_exp_neg_mul_abs_add
-- name    : GlobalTheory.CompanionTheory.TubeFourier.integrable_exp_neg_mul_abs_add
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:16:56.236253+00:00
-- url     : https://prove2.me/theorems/5543b1fc-4c92-4d2a-8ca2-8669582468c2
-- title:
--   Tube Fourier: integrable exp neg mul abs add
-- statement:
--   The Tube Fourier construction uses the integrable exp neg mul abs add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/InverseTransformContinuous.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/InverseTransformContinuous.lean#L16-L20

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussTubeOfTubeGood
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_FInt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InverseTransformContinuous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TubeFourier

theorem GlobalTheory.CompanionTheory.TubeFourier.integrable_exp_neg_mul_abs_add {c : ℝ} (hc : 0 < c) (M : ℝ) :
    Integrable (fun t : ℝ × ℝ => M * Real.exp (-c * (|t.1| + |t.2|))) := by sorry
