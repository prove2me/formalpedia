-- Prove2me | Theorems.Thm_Kyprianou_Ch06_positiveFirstMarkGenuineTwoPositiveIntensities
-- name    : Kyprianou.Ch06.positiveFirstMarkGenuineTwoPositiveIntensities
-- status  : Open
-- author  : @WillR
-- created : 2026-11-16T12:04:58.432192+00:00
-- url     : https://prove2.me/theorems/38a5fc47-4756-4812-a25a-5eb77043b6a0
-- title:
--   positiveFirstMarkGenuineTwoPositiveIntensities genuine residual Chapter 6 obligation
-- statement:
--   Full source proper-overlap positive-rate first A-mark joint distribution for arbitrary outside count cylinders where both A∩C and A\C have strictly positive intensity. Excluded zero-intensity complement cases are independently source-provable from the fact the first A-mark lies in C almost surely; this residual child keeps all genuine two-positive-rate competition and full outside cylinder stochastic dependence.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch06

theorem Kyprianou.Ch06.positiveFirstMarkGenuineTwoPositiveIntensities
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
    (0 < n A →
      ∀ (m : Nat) (times : Fin m → NNReal)
      (B : Fin m → Set E) (counts : Fin m → Nat)
      (t : NNReal) (C : Set E),
      ¬ Disjoint C A →
      ¬ A ⊆ C →
      n (C ∩ A) ≠ 0 →
      n (A \ C) ≠ 0 →
      (∀ i, MeasurableSet (B i) ∧ B i ⊆ Aᶜ ∧ n (B i) < ⊤) →
      MeasurableSet C →
        P {omega | firstMark omega ∈ (some '' C) ∧
          (t : WithTop NNReal) < sigma omega ∧
          (∀ i : Fin m, N omega (times i) (B i) = counts i)} =
          ((n (C ∩ A)) / n A) *
            P {omega | (t : WithTop NNReal) < sigma omega ∧
              (∀ i : Fin m, N omega (times i) (B i) = counts i)}) := by sorry
