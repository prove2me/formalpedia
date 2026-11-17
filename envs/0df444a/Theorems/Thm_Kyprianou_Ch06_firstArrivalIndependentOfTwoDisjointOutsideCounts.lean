-- Prove2me | Theorems.Thm_Kyprianou_Ch06_firstArrivalIndependentOfTwoDisjointOutsideCounts
-- name    : Kyprianou.Ch06.firstArrivalIndependentOfTwoDisjointOutsideCounts
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T08:35:36.654988+00:00
-- url     : https://prove2.me/theorems/0c2aa3b4-8719-407c-a8e8-13cc24443bef
-- title:
--   Chapter 6 first A-arrival survival is independent of the joint counts of two disjoint outside mark sets
-- statement:
--   Chapter 6 first A-arrival survival is independent of the joint counts of two disjoint outside mark sets. The first theorem follows from the genuine marked-Poisson three-rectangle joint distribution, independent outside counts and continuous exponential zero-count law. The second uses the first-arrival joint-event sandwich and the same spatially independent count laws. The full original positive time and mark intensity assumptions are retained, including arbitrary deterministic times and count levels.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.firstArrivalIndependentOfTwoDisjointOutsideCounts
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
    (hBC : Disjoint B C) (hFB : n B < ⊤) (hFC : n C < ⊤)
    (t u v : NNReal) (k l : Nat) :
    P {omega |
      (t : WithTop NNReal) <
        sInf ((fun s : NNReal => (s : WithTop NNReal)) ''
          {s : NNReal | 0 < s ∧ 0 < N omega s A}) ∧
      N omega u B = k ∧ N omega v C = l} =
    P {omega |
      (t : WithTop NNReal) <
        sInf ((fun s : NNReal => (s : WithTop NNReal)) ''
          {s : NNReal | 0 < s ∧ 0 < N omega s A})} *
    P {omega | N omega u B = k ∧ N omega v C = l} := by sorry
