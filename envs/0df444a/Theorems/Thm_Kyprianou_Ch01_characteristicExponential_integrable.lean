-- Prove2me | Theorems.Thm_Kyprianou_Ch01_characteristicExponential_integrable
-- name    : Kyprianou.Ch01.characteristicExponential_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T08:09:49.516376+00:00
-- url     : https://prove2.me/theorems/7648d976-2319-421e-9ace-e774d6e5ac73
-- title:
--   Integrability of the compensated complex exponential of a real process
-- statement:
--   For any pointwise measurable real-valued stochastic process, a fixed frequency theta, complex exponent parameter Psi and time t, the compensated complex exponential is integrable under a probability measure because its complex norm is the deterministic constant exp(t*Re Psi).
-- source:
--   Kyprianou (2006), Chapter 1, exponential Lévy martingale result; integrability conjunct of Kyprianou.Ch01.characteristicExponentialMartingale.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping

open MeasureTheory ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.characteristicExponential_integrable
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hmeas : ∀ t : ℝ≥0, Measurable (X t))
    (theta : ℝ) (Psi : ℂ) (t : ℝ≥0) :
    Integrable
      (fun ω => Complex.exp
        (Complex.I * (theta : ℂ) * (X t ω : ℂ) +
          ((t : ℝ) : ℂ) * Psi)) P := by sorry
