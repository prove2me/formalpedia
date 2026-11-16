-- Prove2me | Theorems.Thm_Kyprianou_Ch01_characteristicExponential_increment_mean_one
-- name    : Kyprianou.Ch01.characteristicExponential_increment_mean_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T09:43:46.743406+00:00
-- url     : https://prove2.me/theorems/a7002f59-252c-4c5a-9e5a-f4c58a8fe1f7
-- title:
--   Compensated Lévy increment characteristic exponential has expectation one
-- statement:
--   For a Lévy process with characteristic exponent Psi, the compensated complex exponential of the increment X_t-X_s, with compensator (t-s)Psi, has expectation one at all ordered times s<=t.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.5, independent-increment martingale proof, stationary-increment characterisation.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch01_levyIncrement_charFun
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.characteristicExponential_increment_mean_one
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hX : IsLevyProcess X P)
    (hmeas : ∀ t : ℝ≥0, Measurable (X t))
    (theta : ℝ) (Psi : ℂ)
    (hchar : ∀ u : ℝ≥0,
      charFun (P.map (X u)) theta =
        Complex.exp (-((u : ℝ) : ℂ) * Psi))
    (s t : ℝ≥0) (hst : s ≤ t) :
    (∫ ω, Complex.exp
      (Complex.I * (theta : ℂ) * ((X t ω - X s ω) : ℂ) +
        (((t - s : ℝ≥0) : ℝ) : ℂ) * Psi) ∂P) = 1 := by sorry
