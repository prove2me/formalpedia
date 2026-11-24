-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TubeFourier_integrable_gaussian_plane
-- name    : GlobalTheory.CompanionTheory.TubeFourier.integrable_gaussian_plane
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:16:30.81588+00:00
-- url     : https://prove2.me/theorems/b1de27d8-d3c9-4c7e-9fba-ca1de461e344
-- title:
--   Tube Fourier: integrable gaussian plane
-- statement:
--   The Tube Fourier construction uses the integrable gaussian plane property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GaussianTubeTransformContinuous.lean#L12-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GaussianTubeTransformContinuous.lean#L12-L22

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussTubeOfTubeGood
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussianTubeTransformContinuous
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

theorem GlobalTheory.CompanionTheory.TubeFourier.integrable_gaussian_plane :
    Integrable (fun y : ℝ × ℝ => Real.exp (-(y.1 ^ 2 + y.2 ^ 2))) (volume : Measure (ℝ × ℝ)) := by sorry
