-- Prove2me | Theorems.Thm_GlobalTheory_T_fourier_parameter_derivative
-- name    : GlobalTheory.T.fourier_parameter_derivative
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:32:04.109301+00:00
-- url     : https://prove2.me/theorems/bab14cce-2e36-4a38-bbe8-dc14c7557a55
-- title:
--   T: fourier parameter derivative
-- statement:
--   The T construction uses the fourier parameter derivative property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FourierParameterDerivativeStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FourierParameterDerivativeStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierParameterDerivative
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierParameterDerivativeStatement
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

theorem GlobalTheory.T.fourier_parameter_derivative : ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (g : X → ℂ) (M : X → ℝ), Measurable M → Integrable g μ → Integrable (fun y => (M y : ℂ) * g y) μ → ∀ s : ℝ, HasDerivAt (fun t : ℝ => ∫ y, g y * Complex.exp (2 * Real.pi * Complex.I * ((t * M y : ℝ) : ℂ)) ∂μ) (2 * Real.pi * Complex.I * ∫ y, (M y : ℂ) * g y * Complex.exp (2 * Real.pi * Complex.I * ((s * M y : ℝ) : ℂ)) ∂μ) s := by sorry
