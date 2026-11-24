-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TubeFourier_norm_exp_sq
-- name    : GlobalTheory.CompanionTheory.TubeFourier.norm_exp_sq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:15:49.701839+00:00
-- url     : https://prove2.me/theorems/044cc2f1-8718-488c-8cb2-7aeba64283f5
-- title:
--   Tube Fourier: norm exp sq
-- statement:
--   The Tube Fourier construction uses the norm exp sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GaussTubeOfTubeGood.lean#L36-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GaussTubeOfTubeGood.lean#L36-L41

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussTubeOfTubeGood
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TubeFourier
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem GlobalTheory.CompanionTheory.TubeFourier.norm_exp_sq (l : ℂ × ℂ) : ‖Complex.exp (l.1 ^ 2 + l.2 ^ 2)‖ =
    Real.exp (l.1.re ^ 2 + l.2.re ^ 2) * Real.exp (-(l.1.im ^ 2 + l.2.im ^ 2)) := by sorry
