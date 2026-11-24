-- Prove2me | Theorems.Thm_Kyprianou_Ch03_prod_expClock_randomThresholdV1
-- name    : Kyprianou.Ch03.prod_expClock_randomThresholdV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T10:09:23.995566+00:00
-- url     : https://prove2.me/theorems/e7615c25-61ff-4f34-bf1a-1f06850e5e0e
-- title:
--   Independent exponential clock above a measurable extended threshold
-- statement:
--   An arbitrary measurable extended nonnegative threshold, independent of a clock in the product measure, gives the exponential survival integral even when the clock is only specified by outer-measure tails. Write the comparison as a countable union of rational cut rectangles and apply the countable measurable-left rectangle lemma. Its sections are the known tails, so their outer measures are measurable and finite, and integral_toReal applies. This is the generic measure-theoretic step, separate from the Levy path and positive root arguments.
-- source:
--   Kyprianou (2006), Chapter 3, Exercise 3.6.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.prod_expClock_randomThresholdV1
    {Omega OmegaE : Type} [MeasurableSpace Omega] [MeasurableSpace OmegaE]
    (P : Measure Omega) (Q : Measure OmegaE)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (tau : Omega → WithTop NNReal) (htau : Measurable tau)
    (q : ℝ) (hq : 0 < q) (e : OmegaE → NNReal)
    (hExponential : ∀ t : NNReal,
      (Q {z : OmegaE | t < e z}).toReal = Real.exp (-q * (t : ℝ))) :
    ((P.prod Q) {z : Omega × OmegaE | tau z.1 < (e z.2 : WithTop NNReal)}).toReal =
      ∫ w, if tau w = ⊤ then (0 : ℝ)
        else Real.exp (-q * (((tau w).untopD (0 : NNReal) : NNReal) : ℝ)) ∂P := by sorry
