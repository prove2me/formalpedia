-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianFirstUpperPassageAlmostSureFinitePublic
-- name    : Kyprianou.Ch01.inverseGaussianFirstUpperPassageAlmostSureFinitePublic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T07:19:04.788766+00:00
-- url     : https://prove2.me/theorems/5b4135de-4416-42b3-b9ff-fe2c25285316
-- title:
--   Positive-drift Brownian upper first passage is almost surely finite
-- statement:
--   For drift b>0 and unit-volatility Brownian motion, first upper passage of every positive level occurs in finite time with probability one. Deduce this from the already proved zero-discount inverse-Gaussian passage transform with integrability and expectation one, where the Laplace payoff is the indicator that passage is finite. The complement is nonnegative, integrable, and expectation zero.
-- source:
--   Kyprianou (2006), Chapter 1 inverse Gaussian passage process, positive drift.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianZeroDiscountPositiveDrift
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianFirstUpperPassageAlmostSureFinitePublic
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (b s : ℝ)
    (hb : 0 < b) (hs : 0 < s)
    (hB : IsLinearBrownian P X 1 b)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t)) :
    ∀ᵐ ω ∂P, firstUpperPassage X s ω ≠ ⊤ := by sorry
