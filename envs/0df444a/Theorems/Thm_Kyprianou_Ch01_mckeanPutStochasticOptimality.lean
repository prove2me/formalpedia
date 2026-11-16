-- Prove2me | Theorems.Thm_Kyprianou_Ch01_mckeanPutStochasticOptimality
-- name    : Kyprianou.Ch01.mckeanPutStochasticOptimality
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T07:49:14.40523+00:00
-- url     : https://prove2.me/theorems/781ac8d5-bc9e-4baa-b783-b9035f85d750
-- title:
--   McKean optimal stopping: probabilistic verification of the Brownian perpetual put barrier
-- statement:
--   Under the exact Brownian process and path assumptions of Kyprianou Chapter 1 Exercise 1.10, establish that the lower barrier is a natural stopping time, its discounted put payoff is integrable, its expected value equals the McKean candidate, and no other natural stopping time has greater expected payoff.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.10; exact four stochastic conjuncts of source theorem Kyprianou.Ch01.mckeanBrownianPutOptimal.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.mckeanPutStochasticOptimality
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
    let tauStar : Ω → WithTop ℝ≥0 :=
      firstLowerPassage X x barrier
    IsNaturalStoppingTime (fun t ω => x + X t ω) tauStar ∧
      Integrable (discountedPut X x K q tauStar) P ∧
      (∫ ω, discountedPut X x K q tauStar ω ∂P) =
        mckeanValue K barrier phi x ∧
      (∀ tau : Ω → WithTop ℝ≥0,
        IsNaturalStoppingTime (fun t ω => x + X t ω) tau →
        (∫ ω, discountedPut X x K q tau ω ∂P) ≤
          mckeanValue K barrier phi x) := by sorry
