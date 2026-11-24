-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TubeFourier_inv_bounded_on_tube
-- name    : GlobalTheory.CompanionTheory.TubeFourier.inv_bounded_on_tube
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:15:55.022821+00:00
-- url     : https://prove2.me/theorems/dadd036c-c50e-4e51-8ec1-a64079824737
-- title:
--   Tube Fourier: inv bounded on tube
-- statement:
--   The Tube Fourier construction uses the inv bounded on tube property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/InverseTransformLocallyBounded.lean#L10-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/InverseTransformLocallyBounded.lean#L10-L37

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussTubeOfTubeGood
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExponentialFourierIntegralBoundStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InverseTransformLocallyBounded
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

theorem GlobalTheory.CompanionTheory.TubeFourier.inv_bounded_on_tube : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (T : Type) [TopologicalSpace T]
    (φ : ℝ × ℝ → T → X), ExpDecay φ → (∀ g : T, Continuous fun t => φ t g) → ∀ C : Set (ℝ × ℝ), IsCompact C →
    ∀ g : T, ∃ U ∈ 𝓝 g, ∃ M : ℝ, ∀ l ∈ tube C, ∀ g' ∈ U, ‖inv (fun t => φ t g') l‖ ≤ M := by sorry
