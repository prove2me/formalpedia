-- Prove2me | Theorems.Thm_Kyprianou_Ch01_mckeanExpectedPutAboveBarrier
-- name    : Kyprianou.Ch01.mckeanExpectedPutAboveBarrier
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T15:24:40.122687+00:00
-- url     : https://prove2.me/theorems/cd0465f2-d518-4fec-a7e7-a59612f92991
-- title:
--   Expected discounted Brownian put reward from a point strictly above a lower exercise barrier
-- statement:
--   For a drifted Brownian process beginning at zero and a starting log-price strictly above an in-the-money lower exercise barrier, the discounted payoff at its first strict lower crossing is integrable and has expectation (K minus exp barrier) multiplied by the exponential Laplace transform of the passage time. It follows by combining the proved pathwise first-passage contact reward identity with the proved shifted Brownian Laplace transform.
-- source:
--   Kyprianou (2006), Chapter 1 Theorem 1.13; optimal exercise barrier expected reward.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.mckeanExpectedPutAboveBarrier
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (sigma gamma K q x barrier : ℝ)
    (hsigma : 0 < sigma) (hq : 0 < q)
    (hxb : barrier < x) (hKbarrier : Real.exp barrier ≤ K)
    (hB : IsLinearBrownian P X sigma gamma)
    (hXmeas : ∀ t : ℝ≥0, Measurable (X t))
    (hAllContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω)) :
    Integrable (discountedPut X x K q (firstLowerPassage X x barrier)) P ∧
      (∫ ω, discountedPut X x K q (firstLowerPassage X x barrier) ω ∂P) =
        (K - Real.exp barrier) *
          Real.exp (-(x - barrier) *
            ((Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) + gamma) /
              sigma ^ 2)) := by sorry
