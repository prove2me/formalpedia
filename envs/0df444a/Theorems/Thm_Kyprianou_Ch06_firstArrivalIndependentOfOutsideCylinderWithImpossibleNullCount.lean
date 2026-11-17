-- Prove2me | Theorems.Thm_Kyprianou_Ch06_firstArrivalIndependentOfOutsideCylinderWithImpossibleNullCount
-- name    : Kyprianou.Ch06.firstArrivalIndependentOfOutsideCylinderWithImpossibleNullCount
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T12:07:21.692808+00:00
-- url     : https://prove2.me/theorems/39d183ce-8cce-4904-b16e-f8d6d681038a
-- title:
--   First A-arrival independent of impossible outside cylinder with positive count on a null-intensity mark
-- statement:
--   For any original Chapter 6 marked Poisson point process and arbitrary finite outside-A count cylinder, if some measurable outside mark set has intensity zero but its requested integer count is positive, then that cylinder is almost surely empty, so it is independent of first A-arrival survival after any time. The proof uses only the source-faithful authoritatively Proved zero-intensity-all-times count theorem, null-event measure comparison, and the unchanged original mark/time/process hypotheses. It covers all cylinder lengths, arbitrary overlapping outside marks, all observation times and all other count levels.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.firstArrivalIndependentOfOutsideCylinderWithImpossibleNullCount
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (n : Measure E) (N : Omega → NNReal → Set E → Nat)
    (A : Set E) (firstMark : Omega → Option E)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (hA : MeasurableSet A) (hFA : n A < ⊤)
    (hMark : ∀ᵐ omega ∂P,
      let sigma : WithTop NNReal :=
        sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
          {v : NNReal | 0 < v ∧ 0 < N omega v A})
      (sigma = ⊤ → firstMark omega = none) ∧
      (sigma ≠ ⊤ → ∃ x : E,
        firstMark omega = some x ∧ x ∈ A ∧
        0 < N omega (sigma.untopD 0) {x}))
    (m : Nat) (times : Fin m → NNReal) (B : Fin m → Set E)
    (counts : Fin m → Nat)
    (hB : ∀ i, MeasurableSet (B i) ∧ B i ⊆ Aᶜ ∧ n (B i) < ⊤)
    (hBad : ∃ i : Fin m, n (B i) = 0 ∧ 0 < counts i)
    (t : NNReal) :
    P {omega | (t : WithTop NNReal) <
        sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
          {v : NNReal | 0 < v ∧ 0 < N omega v A}) ∧
      (∀ j : Fin m, N omega (times j) (B j) = counts j)} =
    P {omega | (t : WithTop NNReal) <
        sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
          {v : NNReal | 0 < v ∧ 0 < N omega v A})} *
    P {omega | ∀ j : Fin m,
      N omega (times j) (B j) = counts j} := by sorry
