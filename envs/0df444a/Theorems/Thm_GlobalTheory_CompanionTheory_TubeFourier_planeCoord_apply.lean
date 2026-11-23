-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TubeFourier_planeCoord_apply
-- name    : GlobalTheory.CompanionTheory.TubeFourier.planeCoord_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:34:03.87804+00:00
-- url     : https://prove2.me/theorems/78ecf19b-57d5-46c5-a144-7c8ba18dc697
-- title:
--   Tube Fourier: plane Coord apply
-- statement:
--   The Tube Fourier construction uses the plane Coord apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FourierInversionProd.lean#L15-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FourierInversionProd.lean#L15-L15

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

theorem GlobalTheory.CompanionTheory.TubeFourier.planeCoord_apply (v : EuclideanSpace ℝ (Fin 2)) : planeCoord v = (v 0, v 1) := by sorry
