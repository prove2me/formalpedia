-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TubeFourier_continuous_pt_shiftSnd
-- name    : GlobalTheory.CompanionTheory.TubeFourier.continuous_pt_shiftSnd
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:16:31.500473+00:00
-- url     : https://prove2.me/theorems/66550947-89e4-4938-8b1f-88dae960a482
-- title:
--   Tube Fourier: continuous pt shift Snd
-- statement:
--   The Tube Fourier construction uses the continuous pt shift Snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TubeTransformVerticalInvariance.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TubeTransformVerticalInvariance.lean#L19-L21

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussTubeOfTubeGood
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContourShiftGaussianDecayStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TubeTransformVerticalInvariance
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

theorem GlobalTheory.CompanionTheory.TubeFourier.continuous_pt_shiftSnd (x : ℝ × ℝ) : Continuous fun y : ℝ × ℝ => pt x y := by sorry
