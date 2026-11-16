-- Prove2me | Theorems.Thm_Kyprianou_Ch01_brownianRealExpMoment
-- name    : Kyprianou.Ch01.brownianRealExpMoment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T14:45:49.542878+00:00
-- url     : https://prove2.me/theorems/2d743b03-36f9-4175-80e5-9b7d68866da5
-- title:
--   Gaussian real exponential moment and integrability for drifted Brownian motion
-- statement:
--   For a drifted Brownian motion specified by Gaussian characteristic exponent, the real exponential at time t is integrable and has exact Gaussian moment generating function exp(t*(sigma squared theta squared/2 + gamma theta)). This is the probability-distribution ingredient in Exercise 1.10(i).
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.10(i), Brownian exponential martingale

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.brownianRealExpMoment
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (sigma gamma theta : ℝ)
    (hsigma : 0 < sigma)
    (hX : IsLinearBrownian P X sigma gamma)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t))
    (t : ℝ≥0) :
    Integrable (fun ω => Real.exp (theta * X t ω)) P ∧
      (∫ ω, Real.exp (theta * X t ω) ∂P) =
        Real.exp ((sigma ^ 2 * theta ^ 2 / 2 + gamma * theta) * (t : ℝ)) := by sorry
