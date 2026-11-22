-- Prove2me | Theorems.Thm_Kyprianou_Ch01_mckeanDiscountedRightBrownianConditionalExpectationLe
-- name    : Kyprianou.Ch01.mckeanDiscountedRightBrownianConditionalExpectationLe
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T19:11:04.828121+00:00
-- url     : https://prove2.me/theorems/160969ae-8b9d-4d8e-8e27-b603df24d99a
-- title:
--   Brownian McKean discounted value satisfies the genuine right-natural conditional expectation inequality
-- statement:
--   The actual stochastic source of Brownian perpetual American put verification. Under the source-faithful drifted Brownian Lévy characteristic exponent, positive volatility and discount, and the exact right-natural filtration, the discounted explicit McKean candidate value satisfies E[M_t | F_s]≤M_s almost surely for all nonnegative s≤t, with M_t=e^{-qt}V(x+X_t). Establish via a stopped Itô/Tanaka or semigroup proof with smooth fit at b, the proved characteristic root giving (L-q)V=0 in continuation, and the proved nonpositive generator inequality in exercise, with localisation and conditional-expectation justification. All process, filtration and Brownian assumptions are preserved. This theorem is the genuine remaining probability/stochastic-calculus obligation for the original McKean optimal stopping proof; adaptedness and integrability are independently proved.
-- source:
--   Kyprianou (2006), Chapter 1 Theorem 1.13; conditional Brownian superharmonic verification.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousFiltration
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.mckeanDiscountedRightBrownianConditionalExpectationLe
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (sigma gamma K q x : ℝ)
    (hsigma : 0 < sigma) (hK : 0 < K) (hq : 0 < q)
    (hB : IsLinearBrownian P X sigma gamma)
    (hXmeas : ∀ t : ℝ≥0, Measurable (X t))
    (hAllContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω))
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (hF : ∀ t, F t = naturalSigmaRight (fun u ω => x + X u ω) t) :
    let phi : ℝ :=
      (Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) + gamma) / sigma ^ 2
    let barrier : ℝ := Real.log (K * phi / (1 + phi))
    ∀ s t : ℝ≥0, s ≤ t →
      P[(fun ω => Real.exp (-q * (t : ℝ)) *
        mckeanValue K barrier phi (x + X t ω)) | F s] ≤ᵐ[P]
      (fun ω => Real.exp (-q * (s : ℝ)) *
        mckeanValue K barrier phi (x + X s ω)) := by sorry
