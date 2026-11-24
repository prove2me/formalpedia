-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Analysis_OscPhase_hasDerivAt_integral_oscillating_phase
-- name    : GlobalTheory.CompanionTheory.Analysis.OscPhase.hasDerivAt_integral_oscillating_phase
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:18:41.841641+00:00
-- url     : https://prove2.me/theorems/47791401-13e8-4e35-abc7-c4bd154df994
-- title:
--   Osc Phase: has Deriv At integral oscillating phase
-- statement:
--   The Osc Phase construction uses the has Deriv At integral oscillating phase property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FourierParameterDerivative.lean#L11-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FourierParameterDerivative.lean#L11-L43

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierParameterDerivative
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Analysis GlobalTheory.CompanionTheory.Analysis.OscPhase

theorem GlobalTheory.CompanionTheory.Analysis.OscPhase.hasDerivAt_integral_oscillating_phase
    (X : Type) [MeasurableSpace X] (μ : Measure X) (g : X → ℂ) (M : X → ℝ)
    (hM : Measurable M) (hg : Integrable g μ)
    (hMg : Integrable (fun y => (M y : ℂ) * g y) μ) (s : ℝ) :
    HasDerivAt (fun t : ℝ => ∫ y, g y * Complex.exp (2 * Real.pi * Complex.I * ((t * M y : ℝ) : ℂ)) ∂μ)
      (2 * Real.pi * Complex.I * ∫ y, (M y : ℂ) * g y * Complex.exp (2 * Real.pi * Complex.I * ((s * M y : ℝ) : ℂ)) ∂μ) s := by sorry
