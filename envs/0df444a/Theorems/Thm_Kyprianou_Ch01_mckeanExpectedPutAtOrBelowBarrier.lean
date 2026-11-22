-- Prove2me | Theorems.Thm_Kyprianou_Ch01_mckeanExpectedPutAtOrBelowBarrier
-- name    : Kyprianou.Ch01.mckeanExpectedPutAtOrBelowBarrier
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T15:28:53.383535+00:00
-- url     : https://prove2.me/theorems/dc1c925d-5f77-43ad-86fb-5e7c358baf92
-- title:
--   Brownian perpetual put immediate exercise reward at or below barrier
-- statement:
--   For a drifted Brownian log-price initially at or below an in-the-money exercise barrier, the strict lower passage occurs at time zero almost surely and the initial put payoff is K minus exp x. The discounted reward is therefore almost surely constant, integrable, and its expectation equals immediate exercise value. This covers both the strict interior and the boundary x=barrier.
-- source:
--   Kyprianou (2006), Chapter 1 Theorem 1.13; immediate exercise and Brownian regularity at barrier.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.mckeanExpectedPutAtOrBelowBarrier
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (sigma gamma K q x barrier : ℝ)
    (hsigma : 0 < sigma) (hK : 0 < K) (hq : 0 < q)
    (hxb : x ≤ barrier) (hKbarrier : Real.exp barrier ≤ K)
    (hB : IsLinearBrownian P X sigma gamma)
    (hXmeas : ∀ t : ℝ≥0, Measurable (X t)) :
    Integrable (discountedPut X x K q (firstLowerPassage X x barrier)) P ∧
      (∫ ω, discountedPut X x K q (firstLowerPassage X x barrier) ω ∂P) =
        K - Real.exp x := by sorry
