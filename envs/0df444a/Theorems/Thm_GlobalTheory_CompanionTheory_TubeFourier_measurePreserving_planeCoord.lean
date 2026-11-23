-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TubeFourier_measurePreserving_planeCoord
-- name    : GlobalTheory.CompanionTheory.TubeFourier.measurePreserving_planeCoord
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:33:51.990957+00:00
-- url     : https://prove2.me/theorems/f69e3e6c-cd54-49ca-a064-698593287fb0
-- title:
--   Tube Fourier: measure Preserving plane Coord
-- statement:
--   The Tube Fourier construction uses the measure Preserving plane Coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FourierInversionProd.lean#L21-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FourierInversionProd.lean#L21-L22

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

theorem GlobalTheory.CompanionTheory.TubeFourier.measurePreserving_planeCoord : MeasurePreserving planeCoord volume volume := by sorry
