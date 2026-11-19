-- Prove2me | Theorems.Thm_Kyprianou_Ch01_brownianUpperZeroBarrierLaplaceOne
-- name    : Kyprianou.Ch01.brownianUpperZeroBarrierLaplaceOne
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T00:30:07.473904+00:00
-- url     : https://prove2.me/theorems/dba4eeea-91d1-41fd-86f2-72e4962fa28b
-- title:
--   Brownian zero-barrier strict upper-passage transform has unit expectation
-- statement:
--   The original discounted first strict upper passage of Brownian motion across its starting level zero is integrable and has expectation exactly one. Use the proved positive-barrier Laplace transform exp(-a kappa), barrier monotonicity, pointwise payoff bound and the exponential lower-bound limit as a↓0. No first-passage distribution or zero-regularity axiom is introduced.
-- source:
--   Kyprianou (2006) Chapter 1 Exercise 1.10(ii), exact zero-barrier endpoint from strictly positive barrier Laplace transforms.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.brownianUpperZeroBarrierLaplaceOne
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (sigma gamma q : ℝ)
    (hsigma : 0 < sigma) (hq : 0 < q)
    (hX : IsLinearBrownian P X sigma gamma)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t)) :
    Integrable (passageLaplace (firstUpperPassage X 0) q) P ∧
    (∫ ω, passageLaplace (firstUpperPassage X 0) q ω ∂P) = 1 := by
  sorry
