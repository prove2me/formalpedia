-- Prove2me | Theorems.Thm_GlobalTheory_T_fourier_one_parameter_integral
-- name    : GlobalTheory.T.fourier_one_parameter_integral
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:31:57.85128+00:00
-- url     : https://prove2.me/theorems/bcee152a-0b07-44e5-b4f1-52536fdde954
-- title:
--   T: fourier one parameter integral
-- statement:
--   The T construction uses the fourier one parameter integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FourierOneParameterIntegralStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FourierOneParameterIntegralStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierOneParameterIntegral
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierOneParameterIntegralStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.fourier_one_parameter_integral : ∀ (A : Type) [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [MeasurableSpace A] [BorelSpace A] (lam : Measure A) [lam.IsAddHaarMeasure] [SFinite lam] (c : ℝ →+ A), Continuous c → ∀ (F G : A → ℂ), Continuous F → Continuous G → Integrable F lam → Integrable G lam → ∀ (χ : AddChar A ℂ), Continuous χ → (∀ x, ‖χ x‖ = 1) → ∀ (f : ℝ), (∀ s : ℝ, χ (c s) = Complex.exp (-(2 * Real.pi * Complex.I * ((s * f : ℝ) : ℂ)))) → (∀ (b : A) (s : ℝ), HasDerivAt (fun t : ℝ => F (b + c t)) (2 * Real.pi * Complex.I * G (b + c s)) s) → ∫ b, G b * χ b ∂lam = (f : ℂ) * ∫ b, F b * χ b ∂lam := by sorry
