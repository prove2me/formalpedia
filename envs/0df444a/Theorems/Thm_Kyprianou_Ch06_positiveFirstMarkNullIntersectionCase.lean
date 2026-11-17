-- Prove2me | Theorems.Thm_Kyprianou_Ch06_positiveFirstMarkNullIntersectionCase
-- name    : Kyprianou.Ch06.positiveFirstMarkNullIntersectionCase
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T11:55:45.71809+00:00
-- url     : https://prove2.me/theorems/8eb56545-d4f6-4e2d-af28-33817392ca55
-- title:
--   Kyprianou Chapter 6 full first-mark and outside-cylinder identity for zero-intensity test-mark intersection
-- statement:
--   For the original positive-rate marked Poisson first-mark theorem, with arbitrary outside-A finite-dimensional count cylinder and any measurable test mark set C satisfying n(C∩A)=0, the full source first-mark joint identity follows because firstMark lies in C with probability zero; the normalised intensity ratio n(C∩A)/n(A) is also zero. Retains all source Poisson process, first-mark selection, positive rate, outside cylinder and observation-time assumptions, with no further independence premise.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.positiveFirstMarkNullIntersectionCase
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
      n (C ∩ A) = 0 →
      (∀ i, MeasurableSet (B i) ∧ B i ⊆ Aᶜ ∧ n (B i) < ⊤) →
      MeasurableSet C →
        P {omega | firstMark omega ∈ (some '' C) ∧
          (t : WithTop NNReal) < sigma omega ∧
          (∀ i : Fin m, N omega (times i) (B i) = counts i)} =
          ((n (C ∩ A)) / n A) *
            P {omega | (t : WithTop NNReal) < sigma omega ∧
              (∀ i : Fin m, N omega (times i) (B i) = counts i)}) := by sorry
