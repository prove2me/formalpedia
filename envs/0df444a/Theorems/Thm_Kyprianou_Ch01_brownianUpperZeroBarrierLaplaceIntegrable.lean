-- Prove2me | Theorems.Thm_Kyprianou_Ch01_brownianUpperZeroBarrierLaplaceIntegrable
-- name    : Kyprianou.Ch01.brownianUpperZeroBarrierLaplaceIntegrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T00:25:20.1172+00:00
-- url     : https://prove2.me/theorems/afd3dd5b-3581-49d8-9a73-6cfa24c246e6
-- title:
--   Brownian zero-barrier upper-passage discounted payoff is integrable
-- statement:
--   For a nondegenerate continuous almost-sure Brownian Lévy process with arbitrary drift, the source strict first-upcrossing of zero has a discounted payoff which is integrable. The original passage time equals a measurable rational infimum on almost all continuous paths, while the payoff is bounded by one. This covers the exact zero-level endpoint missing from the positive-barrier theorem.
-- source:
--   Kyprianou (2006) Chapter 1 Exercise 1.10, original Brownian first-passage transform at zero, measurable rational infimum plus bounded passage payoff.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.brownianUpperZeroBarrierLaplaceIntegrable
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (sigma gamma q : ℝ)
    (hsigma : 0 < sigma) (hq : 0 < q)
    (hX : IsLinearBrownian P X sigma gamma)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t)) :
    Integrable (passageLaplace (firstUpperPassage X 0) q) P := by
  sorry
