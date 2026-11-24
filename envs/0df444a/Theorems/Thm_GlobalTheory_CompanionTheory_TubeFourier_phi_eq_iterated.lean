-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TubeFourier_phi_eq_iterated
-- name    : GlobalTheory.CompanionTheory.TubeFourier.phi_eq_iterated
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:16:41.478873+00:00
-- url     : https://prove2.me/theorems/26da60c2-16b8-4ae5-a2c5-5fa2050594ee
-- title:
--   Tube Fourier: phi eq iterated
-- statement:
--   The Tube Fourier construction uses the phi eq iterated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TubeTransformHorizontalInvariance.lean#L89-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TubeTransformHorizontalInvariance.lean#L89-L96

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussTubeOfTubeGood
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContourShiftGaussianDecayStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TubeTransformHorizontalInvariance
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
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem GlobalTheory.CompanionTheory.TubeFourier.phi_eq_iterated {Ω : Set (ℝ × ℝ)} {G : ℂ × ℂ → X} (hG : GaussTube G Ω) {a b c : ℝ}
    (hs : ∀ s ∈ Set.Icc a b, (s, c) ∈ Ω) (t : ℝ × ℝ) {s : ℝ} (hsm : s ∈ Set.Icc a b) :
    phi G (s, c) t = ∫ y₂ : ℝ, ∫ y₁ : ℝ,
      Complex.exp (-dot (pt (s, c) (y₁, y₂)) t) • G (pt (s, c) (y₁, y₂)) := by sorry
