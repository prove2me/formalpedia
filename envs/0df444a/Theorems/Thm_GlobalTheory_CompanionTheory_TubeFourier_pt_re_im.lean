-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TubeFourier_pt_re_im
-- name    : GlobalTheory.CompanionTheory.TubeFourier.pt_re_im
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:18:49.117798+00:00
-- url     : https://prove2.me/theorems/d9efb502-5795-4123-8210-3fa81e43f723
-- title:
--   Tube Fourier: pt re im
-- statement:
--   The Tube Fourier construction uses the pt re im property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TubeChainHolds.lean#L26-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TubeChainHolds.lean#L26-L27

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

theorem GlobalTheory.CompanionTheory.TubeFourier.pt_re_im (l : ℂ × ℂ) : pt (l.1.re, l.2.re) (l.1.im, l.2.im) = l := by sorry
