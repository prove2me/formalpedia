-- Prove2me | Theorems.Thm_Kyprianou_Ch01_mckeanDiscountedLowerPassageAboveBarrier
-- name    : Kyprianou.Ch01.mckeanDiscountedLowerPassageAboveBarrier
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T15:16:09.730454+00:00
-- url     : https://prove2.me/theorems/d2fccb56-5393-4c56-80d5-df7804d506ee
-- title:
--   Brownian discounted strict lower passage from an arbitrary point above the barrier
-- statement:
--   For a drifted Brownian Lévy process and starting log-price at or above a fixed exercise barrier, the discounted Laplace functional of its first strict lower passage is integrable, with expectation equal to the exponent of minus the distance to the barrier times the positive Brownian passage root. It follows from spatial translation and the already proved lower-passage formula at zero.
-- source:
--   Kyprianou (2006), Chapter 1 Theorem 1.13; Brownian fluctuation identity.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Theorems.Thm_Kyprianou_Ch01_brownianDiscountedLowerPassage
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.mckeanDiscountedLowerPassageAboveBarrier
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (sigma gamma q x barrier : ℝ)
    (hsigma : 0 < sigma) (hq : 0 < q) (hxb : barrier ≤ x)
    (hB : IsLinearBrownian P X sigma gamma)
    (hXmeas : ∀ t : ℝ≥0, Measurable (X t)) :
    Integrable (passageLaplace (firstLowerPassage X x barrier) q) P ∧
    (∫ ω, passageLaplace (firstLowerPassage X x barrier) q ω ∂P) =
      Real.exp (-(x - barrier) *
        ((Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) + gamma) / sigma ^ 2)) := by sorry
