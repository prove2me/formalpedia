-- Prove2me | Theorems.Thm_Kyprianou_Ch01_brownianUpperStoppedExponentialMeanOnePublic
-- name    : Kyprianou.Ch01.brownianUpperStoppedExponentialMeanOnePublic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T09:03:27.596177+00:00
-- url     : https://prove2.me/theorems/6bca63bf-71bd-4ad8-9183-86e05fcf3cc6
-- title:
--   Exercise 1.10(ii) core: stopped Brownian adjustment-root exponential has expectation one
-- statement:
--   For Brownian motion with drift gamma and volatility sigma, positive discount q and positive first-passage level x, the discounted first-upper-passage payoff is integrable and the expectation of exp(theta*x) times this payoff equals one, where theta is the positive adjustment root. This is the optional-stopping and limit identity that the author establishes before isolating the desired Laplace transform. It requires the bounded stopped martingale, convergence and domination; it does not assume the original upper passage transform.
-- source:
--   Kyprianou (2006) Exercise 1.10(ii) worked solution printed page 306, using stopped compensated real exponential martingale, bounded time stopping and dominated convergence. Public dependency required for public target; no mission membership changes.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.brownianUpperStoppedExponentialMeanOnePublic
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (sigma gamma q x : ℝ)
    (hsigma : 0 < sigma) (hq : 0 < q) (hx : 0 < x)
    (hX : IsLinearBrownian P X sigma gamma)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t)) :
    let theta : ℝ :=
      (Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) - gamma) / sigma ^ 2
    Integrable (passageLaplace (firstUpperPassage X x) q) P ∧
    (∫ ω, Real.exp (theta * x) * passageLaplace (firstUpperPassage X x) q ω ∂P) = 1 := by sorry
