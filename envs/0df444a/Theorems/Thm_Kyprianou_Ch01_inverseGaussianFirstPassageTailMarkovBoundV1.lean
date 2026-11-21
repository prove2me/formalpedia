-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianFirstPassageTailMarkovBoundV1
-- name    : Kyprianou.Ch01.inverseGaussianFirstPassageTailMarkovBoundV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T00:06:39.222212+00:00
-- url     : https://prove2.me/theorems/cb3eac91-1001-4aeb-8cdf-751c990e48b6
-- title:
--   Finite-horizon inverse Gaussian passage tail bounded by its Laplace exponent
-- statement:
--   For positive barrier s and nonnegative passage horizon epsilon, the discounted-probability Markov inequality bounds the finite-time survival tail of the possibly infinite first-passage stopping time. In its source-exact normalisation the bound is (1-e^-epsilon) P(T_s>=epsilon) ≤1-exp(-s(sqrt(b²+2)-b)). This follows directly from the proved q=1 inverse-Gaussian Laplace transform, the integrability of passageLaplace, and the deterministic extended-time deficit bound including infinity. The result implies vanishing tail probability as the barrier s decreases to zero, without a Brownian reflection principle.
-- source:
--   Kyprianou (2006), Chapter 1 §1.2.5, q=1 inverse-Gaussian passage Laplace transform and Markov inequality.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianFirstPassageTailMarkovBoundV1
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (b s : ℝ) (hb : 0 < b) (hs : 0 < s)
    (hB : IsLinearBrownian P X 1 b)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t))
    (hContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω))
    (ε : ℝ≥0) :
    (1 - Real.exp (-(ε : ℝ))) *
      (P {ω | (ε : WithTop ℝ≥0) ≤ firstUpperPassage X s ω}).toReal ≤
    1 - Real.exp (-(s * (Real.sqrt (b ^ 2 + 2) - b))) := by
  sorry
