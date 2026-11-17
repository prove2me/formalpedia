-- Prove2me | Theorems.Thm_Kyprianou_Ch06_firstArrivalIndependentOfFiniteTwoOutsideSpacetimeCoordinates
-- name    : Kyprianou.Ch06.firstArrivalIndependentOfFiniteTwoOutsideSpacetimeCoordinates
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T05:31:13.00424+00:00
-- url     : https://prove2.me/theorems/8525b322-0be1-4d0f-adf1-cc64eb26429c
-- title:
--   First A-arrival independent of arbitrary finite outside cylinders using two mark/time coordinates
-- statement:
--   Full Chapter 6 first A-arrival survival independence for arbitrary finite-dimensional outside count cylinders whose observations use at most two marked time-space coordinates (s,B) or (t,C). The two mark sets may overlap; observations can be repeated and count levels arbitrary, including contradictory constraints. The proof derives all finite-dimensional joint count factorisations from the source-proved two-coordinate Poisson law and then transfers zero-A-count factorisation to first arrival, with no new process hypotheses.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.firstArrivalIndependentOfFiniteTwoOutsideSpacetimeCoordinates
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
    (B C : Set E) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hFB : n B < ⊤) (hFC : n C < ⊤)
    (m : Nat) (s t v : NNReal)
    (times : Fin m → NNReal) (marks : Fin m → Set E)
    (hSelect : ∀ i : Fin m,
      (times i = s ∧ marks i = B) ∨
      (times i = t ∧ marks i = C))
    (levels : Fin m → Nat) :
    P {omega | (v : WithTop NNReal) <
      sInf ((fun w : NNReal => (w : WithTop NNReal)) ''
        {w : NNReal | 0 < w ∧ 0 < N omega w A}) ∧
      ∀ i : Fin m, N omega (times i) (marks i) = levels i} =
    P {omega | (v : WithTop NNReal) <
      sInf ((fun w : NNReal => (w : WithTop NNReal)) ''
        {w : NNReal | 0 < w ∧ 0 < N omega w A})} *
      P {omega | ∀ i : Fin m,
        N omega (times i) (marks i) = levels i} := by sorry
