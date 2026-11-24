-- Prove2me | Theorems.Thm_GlobalTheory_eq_zero_of_exp_decay_of_fourier_eq_zero_on_halfLine
-- name    : GlobalTheory.eq_zero_of_exp_decay_of_fourier_eq_zero_on_halfLine
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:19:05.827949+00:00
-- url     : https://prove2.me/theorems/cb9157af-cfb0-4085-8cc2-8f85ef77e8ad
-- title:
--   Global Theory: eq zero of exp decay of fourier eq zero on half Line
-- statement:
--   The Global Theory construction uses the eq zero of exp decay of fourier eq zero on half Line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/EqZeroOfExpDecayOfFourierEqZeroOnHalfLine.lean#L20-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/EqZeroOfExpDecayOfFourierEqZeroOnHalfLine.lean#L20-L91

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FderivIntegralApplyOfHolomorphicOfDominated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IntegrableExpNegMulAbs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EqZeroOfExpDecayOfFourierEqZeroOnHalfLine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped Topology FourierTransform
open GlobalTheory

theorem GlobalTheory.eq_zero_of_exp_decay_of_fourier_eq_zero_on_halfLine :
    ∀ (φ : ℝ → ℂ) (R : ℝ), Continuous φ →
      (∃ A e : ℝ, 0 < e ∧ ∀ s, ‖φ s‖ ≤ A * Real.exp (-(e * |s|))) →
      (∀ ξ : ℝ, R ≤ ξ → ∫ s : ℝ, Complex.exp (-(Complex.I * ξ * s)) * φ s = 0) → φ = 0 := by sorry
