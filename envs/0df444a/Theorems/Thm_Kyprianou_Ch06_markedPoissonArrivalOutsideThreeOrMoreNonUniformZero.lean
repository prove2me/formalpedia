-- Prove2me | Theorems.Thm_Kyprianou_Ch06_markedPoissonArrivalOutsideThreeOrMoreNonUniformZero
-- name    : Kyprianou.Ch06.markedPoissonArrivalOutsideThreeOrMoreNonUniformZero
-- status  : Open
-- author  : @WillR
-- created : 2026-11-16T11:52:23.422792+00:00
-- url     : https://prove2.me/theorems/fb332b4a-d35e-47ac-9a9e-e8ba4d19d8fb
-- title:
--   Chapter 6 A-arrival independence for overlapping outside cylinders of at least three coordinates excluding uniform-time all-zero case
-- statement:
--   For the original marked Poisson process, prove first A-arrival survival independence of finite outside-A count cylinders of at least three coordinates with some overlapping outside mark sets, excluding only the case where all observations are at the same time and all counts are zero. The excluded class has a separate exact proof from the original source finite additivity and singleton outside-mark independence; the remaining child preserves all nontrivial varying-time and nonzero-count cases, arbitrary overlap, and all original source assumptions.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch06

theorem Kyprianou.Ch06.markedPoissonArrivalOutsideThreeOrMoreNonUniformZero
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
    (∀ (m : Nat) (times : Fin m → NNReal)
      (B : Fin m → Set E) (counts : Fin m → Nat) (t : NNReal),
      3 ≤ m →
      (∃ i j : Fin m, i ≠ j ∧ ¬ Disjoint (B i) (B j)) →
      ¬ ((∃ u : NNReal, ∀ i : Fin m, times i = u) ∧
         (∀ i : Fin m, counts i = 0)) →
      (∀ i, MeasurableSet (B i) ∧ B i ⊆ Aᶜ ∧ n (B i) < ⊤) →
        P {omega | (t : WithTop NNReal) < sigma omega ∧
          (∀ i : Fin m, N omega (times i) (B i) = counts i)} =
          P {omega | (t : WithTop NNReal) < sigma omega} *
            P {omega |
              ∀ i : Fin m, N omega (times i) (B i) = counts i}) := by sorry
