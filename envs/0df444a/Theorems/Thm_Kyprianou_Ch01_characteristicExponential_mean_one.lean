-- Prove2me | Theorems.Thm_Kyprianou_Ch01_characteristicExponential_mean_one
-- name    : Kyprianou.Ch01.characteristicExponential_mean_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T08:15:09.000841+00:00
-- url     : https://prove2.me/theorems/9e6138f5-c0c0-43e5-8c62-2b85a10c7242
-- title:
--   Mean-one normalisation of the Lévy characteristic exponential
-- statement:
--   If the characteristic function of a real process at every time t is exp(-t Psi), then the exponentially compensated complex characteristic function has expectation one at every nonnegative time. This is the mean-one consequence of Kyprianou Chapter 1 Exercise 1.5.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.5; expectation-one consequence of its prescribed characteristic exponent and exponential compensation.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

open MeasureTheory ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.characteristicExponential_mean_one
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hmeas : ∀ t : ℝ≥0, Measurable (X t))
    (theta : ℝ) (Psi : ℂ)
    (hchar : ∀ t : ℝ≥0,
      charFun (P.map (X t)) theta =
        Complex.exp (-((t : ℝ) : ℂ) * Psi))
    (t : ℝ≥0) :
    (∫ ω, Complex.exp
      (Complex.I * (theta : ℂ) * (X t ω : ℂ) +
        ((t : ℝ) : ℂ) * Psi) ∂P) = 1 := by sorry
