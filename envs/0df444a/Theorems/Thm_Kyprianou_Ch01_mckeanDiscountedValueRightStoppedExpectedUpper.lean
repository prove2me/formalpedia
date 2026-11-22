-- Prove2me | Theorems.Thm_Kyprianou_Ch01_mckeanDiscountedValueRightStoppedExpectedUpper
-- name    : Kyprianou.Ch01.mckeanDiscountedValueRightStoppedExpectedUpper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T17:01:31.499623+00:00
-- url     : https://prove2.me/theorems/9b534b85-b802-4fc7-803d-98817cac2b0c
-- title:
--   Expected discounted McKean value bounded at every right-natural stopping time
-- statement:
--   For a Brownian Lévy log-price, the discounted McKean candidate value sampled at every possibly infinite right-natural stopping time is integrable and has expectation bounded by the initial candidate. Infinite times contribute zero. Prove a supermartingale property using smooth fit and the proved generator inequalities, then apply continuous-time optional stopping with localisation and bounded convergence. This isolates the substantive stochastic verification from the payoff measurability prerequisite.
-- source:
--   Kyprianou (2006) Chapter 1 Theorem 1.13; right-continuous Brownian optional sampling.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousFiltration
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.mckeanDiscountedValueRightStoppedExpectedUpper
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
      Integrable Z P ∧
        (∫ ω, Z ω ∂P) ≤ mckeanValue K barrier phi x := by sorry
