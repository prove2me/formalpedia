-- Prove2me | Theorems.Thm_Kyprianou_Ch06_firstArrivalIndependentOfThreeRepeatedOutsideMarkCountsAllTimes
-- name    : Kyprianou.Ch06.firstArrivalIndependentOfThreeRepeatedOutsideMarkCountsAllTimes
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T05:26:53.43761+00:00
-- url     : https://prove2.me/theorems/087e3332-35d7-449c-84c6-62d61d63843d
-- title:
--   First A-arrival independent of three repeated outside marks at arbitrary times and counts
-- statement:
--   The original Chapter 6 first A-mark survival event is independent of an arbitrary ordered-or-unordered triple of outside B-count observations at arbitrary deterministic times and count values, where the same mark set B may be repeated in all three coordinates. The full source zero A-count three-time factorisation and first-arrival transfer imply the result directly. The first-arrival Markov/Poisson assumptions and exceptional-set handling are unchanged.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.firstArrivalIndependentOfThreeRepeatedOutsideMarkCountsAllTimes
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
    (B : Set E) (hB : MeasurableSet B)
    (hAB : Disjoint A B) (hFB : n B < ⊤)
    (s t u v : NNReal) (k l q : Nat) :
    P {omega | (v : WithTop NNReal) <
      sInf ((fun w : NNReal => (w : WithTop NNReal)) ''
        {w : NNReal | 0 < w ∧ 0 < N omega w A}) ∧
      N omega s B = k ∧ N omega t B = l ∧ N omega u B = q} =
    P {omega | (v : WithTop NNReal) <
      sInf ((fun w : NNReal => (w : WithTop NNReal)) ''
        {w : NNReal | 0 < w ∧ 0 < N omega w A})} *
      P {omega | N omega s B = k ∧
        N omega t B = l ∧ N omega u B = q} := by sorry
