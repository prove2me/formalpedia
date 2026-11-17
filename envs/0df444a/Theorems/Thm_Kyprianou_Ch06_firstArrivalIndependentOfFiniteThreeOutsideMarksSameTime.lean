-- Prove2me | Theorems.Thm_Kyprianou_Ch06_firstArrivalIndependentOfFiniteThreeOutsideMarksSameTime
-- name    : Kyprianou.Ch06.firstArrivalIndependentOfFiniteThreeOutsideMarksSameTime
-- status  : Open
-- author  : @WillR
-- created : 2026-11-17T05:49:49.939998+00:00
-- url     : https://prove2.me/theorems/7ca2abeb-0b04-42ad-a3a8-e67ab739b867
-- title:
--   First A-arrival independent of arbitrary finite repeated observations from three overlapping outside mark sets at a common time
-- statement:
--   The source Chapter 6 first A-arrival survival event is independent of arbitrary finite-dimensional count cylinders whose coordinates use any of three possibly overlapping outside mark sets B,C,D observed at a common time, with repeated, possibly inconsistent counts. Apply the independently published complete zero-A-count arbitrary finite three-outside-mark factorisation and original source first-arrival continuity transfer. This subsumes all triples at same time and genuinely handles positive spatial overlaps.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.firstArrivalIndependentOfFiniteThreeOutsideMarksSameTime
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
    (B C D : Set E) (hB : MeasurableSet B)
    (hC : MeasurableSet C) (hD : MeasurableSet D)
    (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hAD : Disjoint A D)
    (hFB : n B < ⊤) (hFC : n C < ⊤) (hFD : n D < ⊤)
    (m : Nat) (t u : NNReal) (marks : Fin m → Set E)
    (hSelect : ∀ i : Fin m,
      marks i = B ∨ marks i = C ∨ marks i = D)
    (levels : Fin m → Nat) :
    P {omega | (t : WithTop NNReal) <
      sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
        {v : NNReal | 0 < v ∧ 0 < N omega v A}) ∧
      ∀ i : Fin m, N omega u (marks i) = levels i} =
    P {omega | (t : WithTop NNReal) <
      sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
        {v : NNReal | 0 < v ∧ 0 < N omega v A})} *
      P {omega | ∀ i : Fin m,
        N omega u (marks i) = levels i} := by sorry
