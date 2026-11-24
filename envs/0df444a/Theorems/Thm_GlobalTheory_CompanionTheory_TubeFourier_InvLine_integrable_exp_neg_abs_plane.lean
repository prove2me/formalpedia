-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TubeFourier_InvLine_integrable_exp_neg_abs_plane
-- name    : GlobalTheory.CompanionTheory.TubeFourier.InvLine.integrable_exp_neg_abs_plane
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:15:44.817303+00:00
-- url     : https://prove2.me/theorems/b1b655ef-4e1e-40ad-ac35-1a8798843239
-- title:
--   Inv Line: integrable exp neg abs plane
-- statement:
--   The Inv Line construction uses the integrable exp neg abs plane property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/InverseTransformHolomorphicLines.lean#L10-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/InverseTransformHolomorphicLines.lean#L10-L12

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussTubeOfTubeGood
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExponentialFourierIntegralBound
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InverseTransformHolomorphicLines
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TubeFourier GlobalTheory.CompanionTheory.TubeFourier.InvLine

theorem GlobalTheory.CompanionTheory.TubeFourier.InvLine.integrable_exp_neg_abs_plane {c : ℝ} (hc : 0 < c) :
    Integrable (fun t : ℝ × ℝ => Real.exp (-c * |t.1|) * Real.exp (-c * |t.2|)) := by sorry
