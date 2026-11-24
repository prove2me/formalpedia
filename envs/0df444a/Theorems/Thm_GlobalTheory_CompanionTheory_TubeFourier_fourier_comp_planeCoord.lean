-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TubeFourier_fourier_comp_planeCoord
-- name    : GlobalTheory.CompanionTheory.TubeFourier.fourier_comp_planeCoord
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:16:27.321045+00:00
-- url     : https://prove2.me/theorems/1c283bd0-a3d2-4a09-bba0-279e0c00c0ec
-- title:
--   Tube Fourier: fourier comp plane Coord
-- statement:
--   The Tube Fourier construction uses the fourier comp plane Coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FourierInversionProd.lean#L29-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FourierInversionProd.lean#L29-L41

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

theorem GlobalTheory.CompanionTheory.TubeFourier.fourier_comp_planeCoord {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (h : ℝ × ℝ → X) (w : EuclideanSpace ℝ (Fin 2)) :
    𝓕 (fun v => h (planeCoord v)) w =
      ∫ y : ℝ × ℝ, Complex.exp (-(Complex.I * ((rdot y ((2 * Real.pi) • planeCoord w) : ℝ) : ℂ))) • h y := by sorry
