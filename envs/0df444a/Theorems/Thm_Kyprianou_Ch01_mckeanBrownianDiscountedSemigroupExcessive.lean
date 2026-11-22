-- Prove2me | Theorems.Thm_Kyprianou_Ch01_mckeanBrownianDiscountedSemigroupExcessive
-- name    : Kyprianou.Ch01.mckeanBrownianDiscountedSemigroupExcessive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T20:32:26.955151+00:00
-- url     : https://prove2.me/theorems/a36cf4ad-ef71-4334-a6a6-1cd5234a9c52
-- title:
--   McKean value is q-excessive under the original drifted Brownian semigroup
-- statement:
--   For the actual Brownian Lévy log-surplus, the source McKean value V(y)=K−e^y below the optimal barrier and (K−e^b)e^(−phi(y−b)) above is q-excessive: exponential discount of its Gaussian transition expectation is dominated by its current value at any y. The characteristic root gives (sigma²/2) V''+gamma V'−qV=0 in continuation; in the exercise region this expression is nonpositive; smooth fit eliminates local-time mass. Establish the semigroup inequality using a source-faithful Itô–Tanaka or Gaussian heat-kernel argument. The statement keeps the original Brownian assumptions and exact time difference and kernel, with no unverified model substitution.
-- source:
--   Kyprianou (2006), Ch 1 Thm 1.13, analytic superharmonic verification.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousFiltration
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.mckeanBrownianDiscountedSemigroupExcessive
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (sigma gamma K q x : ℝ)
    (hsigma : 0 < sigma) (hK : 0 < K) (hq : 0 < q)
    (hB : IsLinearBrownian P X sigma gamma)
    (hXmeas : ∀ t : ℝ≥0, Measurable (X t))
    (hAllContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω)) :
    let phi : ℝ :=
      (Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) + gamma) / sigma ^ 2
    let barrier : ℝ := Real.log (K * phi / (1 + phi))
    ∀ s t : ℝ≥0, s ≤ t → ∀ y : ℝ,
      Real.exp (-q * (t : ℝ)) *
        (∫ ξ, mckeanValue K barrier phi (y + X (t - s) ξ) ∂P)
      ≤ Real.exp (-q * (s : ℝ)) * mckeanValue K barrier phi y := by sorry
