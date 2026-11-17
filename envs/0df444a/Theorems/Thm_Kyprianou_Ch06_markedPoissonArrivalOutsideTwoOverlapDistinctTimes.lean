-- Prove2me | Theorems.Thm_Kyprianou_Ch06_markedPoissonArrivalOutsideTwoOverlapDistinctTimes
-- name    : Kyprianou.Ch06.markedPoissonArrivalOutsideTwoOverlapDistinctTimes
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T12:24:27.821578+00:00
-- url     : https://prove2.me/theorems/dd482447-8ed5-451e-842f-fa63d67074c3
-- title:
--   Chapter 6 first A-arrival independent of two overlapping outside mark count observations at distinct times
-- statement:
--   Source-faithful Chapter 6 first A-arrival survival independence from two outside-A marked-Poisson count observations with distinct observation times and overlapping mark sets, preserving arbitrary nonzero count levels, complete original mark-selector and finite-intensity assumptions, the already established non-identical observation case, and the exclusion of nested all-zero cylinders. All same-time overlapping mark count observations are handled by a separately published source-faithful theorem using disjoint spatial atoms; this child isolates the remaining genuinely different-time stochastic dependence.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch06

theorem Kyprianou.Ch06.markedPoissonArrivalOutsideTwoOverlapDistinctTimes
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (A : Set E) (firstMark : Omega → Option E)
    (hPPP : IsMarkedPoissonPointProcess P n N)
    (hA : MeasurableSet A)
    (hFinite : n A < ⊤)
    (hMark : ∀ᵐ omega ∂P,
      let sigma : WithTop NNReal :=
        sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
          {t : NNReal | 0 < t ∧ 0 < N omega t A})
      (sigma = ⊤ → firstMark omega = none) ∧
      (sigma ≠ ⊤ → ∃ x : E,
        firstMark omega = some x ∧ x ∈ A ∧
        0 < N omega (sigma.untopD 0) {x})) :
    let sigma : Omega → WithTop NNReal := fun omega =>
      sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
        {t : NNReal | 0 < t ∧ 0 < N omega t A})
    (∀ (times : Fin 2 → NNReal)
      (B : Fin 2 → Set E) (counts : Fin 2 → Nat) (t : NNReal),
      ¬ Disjoint (B 0) (B 1) →
      ¬ (B 0 = B 1 ∧ times 0 = times 1) →
      ¬ (counts 0 = 0 ∧ counts 1 = 0 ∧
         ((B 0 ⊆ B 1 ∧ times 0 ≤ times 1) ∨
          (B 1 ⊆ B 0 ∧ times 1 ≤ times 0))) →
      times 0 ≠ times 1 →
      (∀ i, MeasurableSet (B i) ∧ B i ⊆ Aᶜ ∧ n (B i) < ⊤) →
        P {omega | (t : WithTop NNReal) < sigma omega ∧
          (∀ i : Fin 2, N omega (times i) (B i) = counts i)} =
          P {omega | (t : WithTop NNReal) < sigma omega} *
            P {omega |
              ∀ i : Fin 2, N omega (times i) (B i) = counts i}) := by sorry
