-- Prove2me | Theorems.Thm_Kyprianou_Ch01_brownianCharFun_reflected
-- name    : Kyprianou.Ch01.brownianCharFun_reflected
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T20:54:51.307387+00:00
-- url     : https://prove2.me/theorems/3f7e5ea2-eb29-4d20-8642-6df09df1bca5
-- title:
--   Reflected Brownian marginals have the original Gaussian variance and opposite drift
-- statement:
--   The characteristic function of the time-t marginal of -X is the characteristic function of X at the negated frequency. The original Gaussian characteristic exponent at frequency -xi changes the sign of the drift and retains the same squared volatility. This is the exact marginal-law component of the Brownian path reflection lemma, with no extra assumptions beyond IsLinearBrownian.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.10(ii), Brownian reflection and Gaussian exponent transformation.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.brownianCharFun_reflected
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (sigma gamma : ℝ)
    (hX : Kyprianou.Ch01.IsLinearBrownian P X sigma gamma) :
    ∀ (t : ℝ≥0) (xi : ℝ),
      charFun (P.map (fun ω => -X t ω)) xi =
        Complex.exp (((t : ℝ) : ℂ) *
          (Complex.I * (((-gamma) * xi : ℝ) : ℂ) -
            (((sigma ^ 2 * xi ^ 2 / 2 : ℝ)) : ℂ))) := by sorry
