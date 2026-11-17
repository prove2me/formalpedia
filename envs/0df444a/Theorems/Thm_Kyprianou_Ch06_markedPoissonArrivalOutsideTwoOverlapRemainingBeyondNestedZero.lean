-- Prove2me | Theorems.Thm_Kyprianou_Ch06_markedPoissonArrivalOutsideTwoOverlapRemainingBeyondNestedZero
-- name    : Kyprianou.Ch06.markedPoissonArrivalOutsideTwoOverlapRemainingBeyondNestedZero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T11:53:11.435125+00:00
-- url     : https://prove2.me/theorems/2cb0d325-d79e-46d6-bc36-b6843fe83591
-- title:
--   Chapter 6 two overlapping outside count observations, excluding source-proved nested all-zero cases
-- statement:
--   Prove first A-arrival survival independent of the two-coordinate cylinder for arbitrary overlapping outside-A marked Poisson count sets and observation times, retaining all original source assumptions and excluding only the case in which both requested counts are zero and one mark set and its observation time are dominated by the other. Those nested zero-count cases are a genuine separately proven consequence of source spatial and temporal monotonicity plus singleton outside count independence. All nonzero, nonnested, and crossing-time overlapping cases remain in this child.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch06

theorem Kyprianou.Ch06.markedPoissonArrivalOutsideTwoOverlapRemainingBeyondNestedZero
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
      (∀ i, MeasurableSet (B i) ∧ B i ⊆ Aᶜ ∧ n (B i) < ⊤) →
        P {omega | (t : WithTop NNReal) < sigma omega ∧
          (∀ i : Fin 2, N omega (times i) (B i) = counts i)} =
          P {omega | (t : WithTop NNReal) < sigma omega} *
            P {omega |
              ∀ i : Fin 2, N omega (times i) (B i) = counts i}) := by sorry
