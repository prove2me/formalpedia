-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TubeFourier_integrable_gauss_one
-- name    : GlobalTheory.CompanionTheory.TubeFourier.integrable_gauss_one
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:16:26.658731+00:00
-- url     : https://prove2.me/theorems/8a0908c0-020f-4305-8f38-e054896bd2d5
-- title:
--   Tube Fourier: integrable gauss one
-- statement:
--   The Tube Fourier construction uses the integrable gauss one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GaussianTubeTransformBound.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GaussianTubeTransformBound.lean#L9-L10

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

theorem GlobalTheory.CompanionTheory.TubeFourier.integrable_gauss_one : Integrable (fun s : ℝ => Real.exp (-s ^ 2)) := by sorry
