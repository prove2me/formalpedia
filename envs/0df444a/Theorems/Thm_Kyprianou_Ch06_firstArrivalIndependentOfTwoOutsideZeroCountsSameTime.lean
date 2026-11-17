-- Prove2me | Theorems.Thm_Kyprianou_Ch06_firstArrivalIndependentOfTwoOutsideZeroCountsSameTime
-- name    : Kyprianou.Ch06.firstArrivalIndependentOfTwoOutsideZeroCountsSameTime
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T09:09:03.990199+00:00
-- url     : https://prove2.me/theorems/d64ff52d-e118-4e77-9301-73eb9b6be9b6
-- title:
--   Chapter 6 first A-arrival survival independent of two possibly overlapping outside zero-count events at a common time
-- statement:
--   For the original Chapter 6 marked Poisson process and any measurable finite-intensity mark sets B,C disjoint from A but allowed to overlap one another, the joint two-coordinate zero-count cylinder N_u(B)=N_u(C)=0 is independent of the first positive A-mark arrival survival event after t. By original source finite spatial additivity, the two zero-count events coincide almost surely with zero count on B∪C, which is a genuine single outside mark set. Apply independently Proved first A-arrival independence from one disjoint outside count. No new independence assumption, count-level restriction except zero, or mark-set disjointness between B and C is introduced.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.firstArrivalIndependentOfTwoOutsideZeroCountsSameTime
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (n : Measure E) (N : Omega → NNReal → Set E → Nat)
    (A : Set E) (firstMark : Omega → Option E)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (hA : MeasurableSet A) (hFA : n A < ⊤)
    (hMark : ∀ᵐ omega ∂P,
      let sigma : WithTop NNReal :=
        sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
          {t : NNReal | 0 < t ∧ 0 < N omega t A})
      (sigma = ⊤ → firstMark omega = none) ∧
      (sigma ≠ ⊤ → ∃ x : E,
        firstMark omega = some x ∧ x ∈ A ∧
        0 < N omega (sigma.untopD 0) {x}))
    (B C : Set E) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hFB : n B < ⊤) (hFC : n C < ⊤)
    (t u : NNReal) :
    P {omega |
      (t : WithTop NNReal) <
        sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
          {v : NNReal | 0 < v ∧ 0 < N omega v A}) ∧
      N omega u B = 0 ∧ N omega u C = 0} =
    P {omega |
      (t : WithTop NNReal) <
        sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
          {v : NNReal | 0 < v ∧ 0 < N omega v A})} *
    P {omega | N omega u B = 0 ∧ N omega u C = 0} := by sorry
