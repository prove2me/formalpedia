-- Prove2me | Theorems.Thm_Kyprianou_Ch06_positiveFirstMarkFullMeasureIntersectionCase
-- name    : Kyprianou.Ch06.positiveFirstMarkFullMeasureIntersectionCase
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T12:00:28.644664+00:00
-- url     : https://prove2.me/theorems/39c2335c-6bce-46a4-9861-14c1e9f789ec
-- title:
--   Full first-mark factorisation when test set C contains full marked A-intensity
-- statement:
--   For the complete original positive-rate Chapter 6 first-mark factorisation, the intensity condition n(A\C)=0 suffices to make the normalised mark factor n(C∩A)/n(A) equal one. At positive A-intensity the selected first mark lies in A almost surely, and because the omitted A\C has zero intensity the mark lies in C almost surely. The first-mark membership condition therefore changes no joint probability with arbitrary outside-A finite-dimensional counts and first-arrival survival. Includes proper-overlap test mark sets that fail A⊆C set-theoretically, while preserving all source quantifiers and stochastic assumptions.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.positiveFirstMarkFullMeasureIntersectionCase
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
      n (A \ C) = 0 →
      (∀ i, MeasurableSet (B i) ∧ B i ⊆ Aᶜ ∧ n (B i) < ⊤) →
      MeasurableSet C →
        P {omega | firstMark omega ∈ (some '' C) ∧
          (t : WithTop NNReal) < sigma omega ∧
          (∀ i : Fin m, N omega (times i) (B i) = counts i)} =
          ((n (C ∩ A)) / n A) *
            P {omega | (t : WithTop NNReal) < sigma omega ∧
              (∀ i : Fin m, N omega (times i) (B i) = counts i)}) := by sorry
