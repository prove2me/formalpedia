-- Prove2me | Theorems.Thm_Kyprianou_Ch01_mckeanRightAllStoppingPayoffUpperBound
-- name    : Kyprianou.Ch01.mckeanRightAllStoppingPayoffUpperBound
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T14:29:06.530571+00:00
-- url     : https://prove2.me/theorems/d840d862-c4c8-48c6-b2ef-462bf0e3d2ba
-- title:
--   McKean right-continuous stopping-time upper value via excessive majorant
-- statement:
--   For every right-natural-filtration stopping time, the expected discounted Brownian perpetual-put payoff is bounded by the McKean candidate value. Prove the value function majorises the payoff, is q-excessive under the Brownian semigroup, and apply optional sampling with localisation followed by bounded convergence.
-- source:
--   Kyprianou (2006), Chapter 1, Theorem 1.13; verification principle for Brownian perpetual American put.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousFiltration
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.mckeanRightAllStoppingPayoffUpperBound
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (sigma gamma K q x : ℝ)
    (hsigma : 0 < sigma) (hK : 0 < K) (hq : 0 < q)
    (hB : IsLinearBrownian P X sigma gamma)
    (hXmeas : ∀ t : ℝ≥0, Measurable (X t))
    (hAllContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω)) :
    let phi : ℝ :=
      (Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) + gamma) /
        sigma ^ 2
    let barrier : ℝ := Real.log (K * phi / (1 + phi))
    ∀ tau : Ω → WithTop ℝ≥0,
      IsNaturalRightStoppingTime (fun t ω => x + X t ω) tau →
      (∫ ω, discountedPut X x K q tau ω ∂P) ≤
        mckeanValue K barrier phi x := by sorry
