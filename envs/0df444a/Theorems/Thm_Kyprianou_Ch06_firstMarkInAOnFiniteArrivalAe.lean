-- Prove2me | Theorems.Thm_Kyprianou_Ch06_firstMarkInAOnFiniteArrivalAe
-- name    : Kyprianou.Ch06.firstMarkInAOnFiniteArrivalAe
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T08:40:20.479701+00:00
-- url     : https://prove2.me/theorems/e9b2c5cd-7a39-493e-a2b4-3a240a30a397
-- title:
--   Chapter 6 first A-mark selection belongs to A on finite arrival, almost surely
-- statement:
--   The original cemetery-or-in-A mark selector in Kyprianou Lemma 6.18 implies that whenever the first positive A-count arrival is finite, the selected first mark is some(x) with x∈A, almost surely. This is the exact support-on-finite-arrival implication needed for the positive-rate first-mark law, without assuming the first arrival is finite or assuming a distribution for the mark.

import Mathlib
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.firstMarkInAOnFiniteArrivalAe
    {Omega E : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (N : Omega → NNReal → Set E → Nat)
    (A : Set E) (firstMark : Omega → Option E)
    (hMark : ∀ᵐ omega ∂P,
      let sigma : WithTop NNReal :=
        sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
          {t : NNReal | 0 < t ∧ 0 < N omega t A})
      (sigma = ⊤ → firstMark omega = none) ∧
      (sigma ≠ ⊤ → ∃ x : E,
        firstMark omega = some x ∧ x ∈ A ∧
        0 < N omega (sigma.untopD 0) {x})) :
    ∀ᵐ omega ∂P,
      (sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
        {t : NNReal | 0 < t ∧ 0 < N omega t A}) ≠ ⊤) →
      firstMark omega ∈ (some '' A) := by sorry
