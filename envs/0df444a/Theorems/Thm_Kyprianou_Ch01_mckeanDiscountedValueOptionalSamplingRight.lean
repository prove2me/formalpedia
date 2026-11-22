-- Prove2me | Theorems.Thm_Kyprianou_Ch01_mckeanDiscountedValueOptionalSamplingRight
-- name    : Kyprianou.Ch01.mckeanDiscountedValueOptionalSamplingRight
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T15:37:37.20191+00:00
-- url     : https://prove2.me/theorems/446404a8-d9db-4bba-bf38-47a2b6c99f07
-- title:
--   Brownian discounted McKean value satisfies optional sampling for all right-natural stopping times
-- statement:
--   For a drifted Brownian Lévy process with positive discount, the McKean value function evaluated at an arbitrary possibly infinite stopping time in the right-continuous natural filtration has an integrable discounted stopped value bounded in expectation by its initial value, while the discounted put payoff is integrable. Infinite stopping times contribute zero. This is the substantive stochastic verification step, via the generator inequality, stopped nonnegative supermartingale, and localisation plus Fatou. Once proved, pointwise domination of put payoff by McKean value implies the universal optimal stopping bound.
-- source:
--   Kyprianou (2006), Chapter 1 Theorem 1.13; Brownian perpetual American put verification, optional stopping under right-continuous natural filtration.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousFiltration
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.mckeanDiscountedValueOptionalSamplingRight
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
      let Z : Ω → ℝ := fun ω =>
        match tau ω with
        | none => 0
        | some t => Real.exp (-q * (t : ℝ)) *
            mckeanValue K barrier phi (x + X t ω)
      Integrable (discountedPut X x K q tau) P ∧
        Integrable Z P ∧
        (∫ ω, Z ω ∂P) ≤ mckeanValue K barrier phi x := by sorry
