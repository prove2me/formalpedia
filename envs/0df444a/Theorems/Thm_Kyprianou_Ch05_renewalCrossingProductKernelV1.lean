-- Prove2me | Theorems.Thm_Kyprianou_Ch05_renewalCrossingProductKernelV1
-- name    : Kyprianou.Ch05.renewalCrossingProductKernelV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T19:02:42.440042+00:00
-- url     : https://prove2.me/theorems/dbd64c42-39d7-5dda-a811-e4bb8a1598b1
-- title:
--   Crossing cell product measure equals the iterated renewal kernel
-- statement:
--   The product law of one renewal epoch and its next mark gives the iterated crossing-cell kernel.
-- source:
--   Kyprianou (2006), Lemma 5.5

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
open MeasureTheory Filter Set ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

open Classical in
theorem Kyprianou.Ch05.renewalCrossingProductKernelV1
    (V F : Measure ℝ) [SFinite F]
    (x : ℝ) (A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hA2 : A ⊆ Ioi 0) :
    (V.prod F) {p : ℝ × ℝ | p.1 ∈ Icc 0 x ∧ p.2-(x-p.1) ∈ A ∧ x-p.1 ∈ B} =
      ∫⁻ v in Icc (0 : ℝ) x,
        (∫⁻ z in Ioi (x-v),
          (if z-(x-v) ∈ A ∧ x-v ∈ B then (1 : ENNReal) else 0) ∂F) ∂V := by
  sorry
