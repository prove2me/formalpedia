-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TubeFourier_re_dot_pt_eq_rdot
-- name    : GlobalTheory.CompanionTheory.TubeFourier.re_dot_pt_eq_rdot
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:18:14.629057+00:00
-- url     : https://prove2.me/theorems/67a998a5-0870-418a-8421-a3e58d8ff8a7
-- title:
--   Tube Fourier: re dot pt eq rdot
-- statement:
--   The Tube Fourier construction uses the re dot pt eq rdot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GaussianTubeTransformContinuous.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GaussianTubeTransformContinuous.lean#L9-L10

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

theorem GlobalTheory.CompanionTheory.TubeFourier.re_dot_pt_eq_rdot (x y t : ℝ × ℝ) : (dot (pt x y) t).re = rdot x t := by sorry
