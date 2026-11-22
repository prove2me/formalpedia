-- Prove2me | Theorems.Thm_Kyprianou_Ch01_mckeanRightBarrierRewardIdentity
-- name    : Kyprianou.Ch01.mckeanRightBarrierRewardIdentity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T14:29:13.075091+00:00
-- url     : https://prove2.me/theorems/1e353ea3-633d-47aa-903e-a89c7baae8a2
-- title:
--   McKean optimal lower barrier discounted reward identity
-- statement:
--   For a Brownian motion with drift and volatility under the original assumptions, the discounted perpetual-put payoff at the McKean lower passage barrier is integrable and has the stated explicit value, including immediate exercise and boundary starting points. Use the proved lower-passage Laplace transform and pointwise payoff bound.
-- source:
--   Kyprianou (2006), Chapter 1, Theorem 1.13; Brownian first passage and McKean optimal exercise value.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.mckeanRightBarrierRewardIdentity
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
    Integrable (discountedPut X x K q tauStar) P ∧
      (∫ ω, discountedPut X x K q tauStar ω ∂P) =
        mckeanValue K barrier phi x := by sorry
