-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TubeFourier_integral_gauss_one
-- name    : GlobalTheory.CompanionTheory.TubeFourier.integral_gauss_one
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:16:43.058847+00:00
-- url     : https://prove2.me/theorems/a55ed6f9-a3f5-4c6e-9750-c9f4156b38f1
-- title:
--   Tube Fourier: integral gauss one
-- statement:
--   The Tube Fourier construction uses the integral gauss one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GaussianTubeTransformBound.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GaussianTubeTransformBound.lean#L12-L13

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussTubeOfTubeGood
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussianTubeTransformBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TubeFourier

theorem GlobalTheory.CompanionTheory.TubeFourier.integral_gauss_one : ∫ s : ℝ, Real.exp (-s ^ 2) = Real.sqrt Real.pi := by sorry
