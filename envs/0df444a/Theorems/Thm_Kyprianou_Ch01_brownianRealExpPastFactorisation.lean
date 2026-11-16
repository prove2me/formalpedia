-- Prove2me | Theorems.Thm_Kyprianou_Ch01_brownianRealExpPastFactorisation
-- name    : Kyprianou.Ch01.brownianRealExpPastFactorisation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T14:45:49.296946+00:00
-- url     : https://prove2.me/theorems/b214090a-5231-4328-a071-c627d6dd9d4f
-- title:
--   Brownian exponential expectation factorisation against a natural-past event
-- statement:
--   Stationary independent Brownian increments imply factorisation of the exponential moment at time t over any event in the natural sigma-algebra at time s, into the increment moment (with stationary law X(t-s)) and the past exponential moment. This is the stochastic independence ingredient in Exercise 1.10(i).
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.10(i), Brownian exponential martingale

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.brownianRealExpPastFactorisation
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (sigma gamma theta : ℝ)
    (hsigma : 0 < sigma)
    (hX : IsLinearBrownian P X sigma gamma)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t))
    (s t : ℝ≥0) (hst : s ≤ t)
    (A : Set Ω)
    (hA : @MeasurableSet Ω (naturalSigma X s) A) :
    (∫ ω in A, Real.exp (theta * X t ω) ∂P) =
      (∫ ω, Real.exp (theta * X (t - s) ω) ∂P) *
        (∫ ω in A, Real.exp (theta * X s ω) ∂P) := by sorry
