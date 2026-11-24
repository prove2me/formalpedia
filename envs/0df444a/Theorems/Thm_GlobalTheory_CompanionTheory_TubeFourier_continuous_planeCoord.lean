-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TubeFourier_continuous_planeCoord
-- name    : GlobalTheory.CompanionTheory.TubeFourier.continuous_planeCoord
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:16:05.656949+00:00
-- url     : https://prove2.me/theorems/b2c878ae-a352-4090-b793-79f7953b8150
-- title:
--   Tube Fourier: continuous plane Coord
-- statement:
--   The Tube Fourier construction uses the continuous plane Coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FourierInversionProd.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FourierInversionProd.lean#L17-L19

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussTubeOfTubeGood
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierInversionProd
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
open scoped FourierTransform
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TubeFourier

theorem GlobalTheory.CompanionTheory.TubeFourier.continuous_planeCoord : Continuous planeCoord := by sorry
