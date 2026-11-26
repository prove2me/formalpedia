-- Prove2me | Theorems.Thm_Kyprianou_Ch05_renewalCrossingEventSumV1
-- name    : Kyprianou.Ch05.renewalCrossingEventSumV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T19:00:08.36384+00:00
-- url     : https://prove2.me/theorems/3bf94303-08d8-496b-a5fc-ac0fdf4e30c1
-- title:
--   The joint renewal passage event is a disjoint sum of crossing-index events
-- statement:
--   The joint renewal passage event is a disjoint sum of crossing-index events
-- source:
--   Kyprianou (2006), Lemma 5.5

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

open Set Kyprianou.Ch05

open Classical in
theorem Kyprianou.Ch05.renewalCrossingEventSumV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Z : ℕ → Omega → ℝ) (F : Measure ℝ)
    (hRenewal : IsRenewalEpochProcess P Z F)
    (x : ℝ) (hx : 0 < x)
    (A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hA2 : A ⊆ Ioi (0 : ℝ)) (hB2 : B ⊆ Ioc (0 : ℝ) x) :
    P {w : Omega | 0 < renewalOvershoot Z x w ∧
      renewalOvershoot Z x w ∈ A ∧ renewalUndershoot Z x w ∈ B} = ∑' n : ℕ, P {w : Omega | renewalEpoch Z n w ∈ Icc (0 : ℝ) x ∧
      x < renewalEpoch Z n w + Z n w ∧
      Z n w - (x - renewalEpoch Z n w) ∈ A ∧ x - renewalEpoch Z n w ∈ B} := by
  sorry
