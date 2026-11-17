-- Prove2me | Theorems.Thm_Kyprianou_Ch06_firstArrivalIndependentOfThreeOrderedRepeatedOutsideMarkCounts
-- name    : Kyprianou.Ch06.firstArrivalIndependentOfThreeOrderedRepeatedOutsideMarkCounts
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T05:25:01.283205+00:00
-- url     : https://prove2.me/theorems/481d7b4b-e6e7-4423-af53-637cf57b239e
-- title:
--   First arrival independent of three ordered same-outside-mark count observations with all levels
-- statement:
--   Full source Chapter 6 first-arrival survival is independent of three ordered observations s≤t≤u of the same outside-A mark set B, with every count level allowed including decreasing invalid levels. Apply source-proved zero A-count triple-cylinder independence at every deterministic time, then source-proved first-arrival transfer from cumulative Poisson zero-count independence. This isolates a genuinely nontrivial m=3 overlapping repeated-mark subcase of Lemma 6.18 without changing its assumptions.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.firstArrivalIndependentOfThreeOrderedRepeatedOutsideMarkCounts
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
    (s t u v : NNReal) (hst : s ≤ t) (htu : t ≤ u)
    (k l q : Nat) :
    P {omega | (v : WithTop NNReal) <
      sInf ((fun w : NNReal => (w : WithTop NNReal)) ''
        {w : NNReal | 0 < w ∧ 0 < N omega w A}) ∧
      N omega s B = k ∧ N omega t B = l ∧ N omega u B = q} =
    P {omega | (v : WithTop NNReal) <
      sInf ((fun w : NNReal => (w : WithTop NNReal)) ''
        {w : NNReal | 0 < w ∧ 0 < N omega w A})} *
      P {omega | N omega s B = k ∧
        N omega t B = l ∧ N omega u B = q} := by sorry
