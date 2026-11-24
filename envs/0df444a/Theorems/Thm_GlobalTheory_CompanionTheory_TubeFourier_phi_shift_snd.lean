-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TubeFourier_phi_shift_snd
-- name    : GlobalTheory.CompanionTheory.TubeFourier.phi_shift_snd
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:18:13.921593+00:00
-- url     : https://prove2.me/theorems/54ffcf28-4ed3-4d3c-8536-1902980c2deb
-- title:
--   Tube Fourier: phi shift snd
-- statement:
--   The Tube Fourier construction uses the phi shift snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TubeTransformVerticalInvariance.lean#L34-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TubeTransformVerticalInvariance.lean#L34-L101

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussTubeOfTubeGood
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContourShiftGaussianDecayStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TubeTransformVerticalInvariance
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TubeFourier

theorem GlobalTheory.CompanionTheory.TubeFourier.phi_shift_snd (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] (Ω : Set (ℝ × ℝ))
    (G : ℂ × ℂ → X) (hG : GaussTube G Ω) (a b c : ℝ) (hab : a ≤ b) (hs : ∀ s ∈ Set.Icc a b, (c, s) ∈ Ω)
    (t : ℝ × ℝ) : phi G (c, a) t = phi G (c, b) t := by sorry
