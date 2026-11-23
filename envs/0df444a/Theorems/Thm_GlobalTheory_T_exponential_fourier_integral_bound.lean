-- Prove2me | Theorems.Thm_GlobalTheory_T_exponential_fourier_integral_bound
-- name    : GlobalTheory.T.exponential_fourier_integral_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:35:56.891844+00:00
-- url     : https://prove2.me/theorems/c40f0e15-83a6-4242-b4fb-df8de9a32a8a
-- title:
--   T: exponential fourier integral bound
-- statement:
--   The T construction uses the exponential fourier integral bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExponentialFourierIntegralBoundStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExponentialFourierIntegralBoundStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExponentialFourierIntegralBound
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussTubeOfTubeGood
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExponentialFourierIntegralBoundStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exponential_fourier_integral_bound : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (φ : ℝ × ℝ → X) (l : ℂ × ℂ) (ε M : ℝ), 0 < ε → Continuous φ → (∀ t : ℝ × ℝ, ‖φ t‖ ≤ M * Real.exp (-rdot (l.1.re, l.2.re) t) * Real.exp (-ε * (|t.1| + |t.2|))) → Integrable (fun t : ℝ × ℝ => Complex.exp (dot l t) • φ t) ∧ ‖∫ t : ℝ × ℝ, Complex.exp (dot l t) • φ t‖ ≤ M * (2 / ε) ^ 2 := by sorry
