-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TubeFourier_continuous_pt
-- name    : GlobalTheory.CompanionTheory.TubeFourier.continuous_pt
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:17:49.4418+00:00
-- url     : https://prove2.me/theorems/ffc17eaa-63f9-4ae8-867d-3d135ec384aa
-- title:
--   Tube Fourier: continuous pt
-- statement:
--   The Tube Fourier construction uses the continuous pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TubeChainHolds.lean#L18-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TubeChainHolds.lean#L18-L24

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussTubeOfTubeGood
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TubeTransformIndependentOfBaseStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussianTubeTransformBoundStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussianTubeTransformContinuousStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExponentialDecayByMidpointsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InverseTransformLocallyBoundedStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InverseTransformContinuousStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InverseTransformHolomorphicLinesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InverseTransformRecoversFunctionStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TubeChainHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TubeFourier

theorem GlobalTheory.CompanionTheory.TubeFourier.continuous_pt (x : ℝ × ℝ) : Continuous fun y : ℝ × ℝ => pt x y := by sorry
