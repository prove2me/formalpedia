-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TubeFourier_continuous_mk_im_shiftSnd
-- name    : GlobalTheory.CompanionTheory.TubeFourier.continuous_mk_im_shiftSnd
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:16:31.227876+00:00
-- url     : https://prove2.me/theorems/ced878de-ef48-4406-bd66-55df5a154a91
-- title:
--   Tube Fourier: continuous mk im shift Snd
-- statement:
--   The Tube Fourier construction uses the continuous mk im shift Snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TubeTransformVerticalInvariance.lean#L12-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TubeTransformVerticalInvariance.lean#L12-L17

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

theorem GlobalTheory.CompanionTheory.TubeFourier.continuous_mk_im_shiftSnd (x : ℝ) : Continuous fun y : ℝ => (⟨x, y⟩ : ℂ) := by sorry
