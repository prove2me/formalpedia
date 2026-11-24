-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TubeFourier_InvLine_dot_add_smul
-- name    : GlobalTheory.CompanionTheory.TubeFourier.InvLine.dot_add_smul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:17:58.637912+00:00
-- url     : https://prove2.me/theorems/88cf1da5-fcf0-4779-827d-792cad0182a8
-- title:
--   Inv Line: dot add smul
-- statement:
--   The Inv Line construction uses the dot add smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/InverseTransformHolomorphicLines.lean#L14-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/InverseTransformHolomorphicLines.lean#L14-L17

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

theorem GlobalTheory.CompanionTheory.TubeFourier.InvLine.dot_add_smul (p v : ℂ × ℂ) (τ : ℂ) (t : ℝ × ℝ) :
    dot (p + τ • v) t = dot p t + τ * dot v t := by sorry
