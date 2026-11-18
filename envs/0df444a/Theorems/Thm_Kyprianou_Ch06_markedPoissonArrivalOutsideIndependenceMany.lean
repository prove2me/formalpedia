-- Prove2me | Theorems.Thm_Kyprianou_Ch06_markedPoissonArrivalOutsideIndependenceMany
-- name    : Kyprianou.Ch06.markedPoissonArrivalOutsideIndependenceMany
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T08:28:06.67502+00:00
-- url     : https://prove2.me/theorems/8db5db8d-bd93-42ee-be10-e991336fecb1
-- title:
--   Chapter 6 first Poisson A-arrival independent of finite outside-mark cylinders of size at least two
-- statement:
--   Under all original marked Poisson process and first-mark assumptions of Lemma 6.18, prove the full outside-mark finite-dimensional cylinder independence at arbitrary observation times for every family of at least two measurable finite-intensity outside-A mark sets, including overlapping sets and repeated times. This is the genuinely unproved many-coordinate case after separately treating empty and singleton cylinders, and it preserves all source quantifiers.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch06

theorem Kyprianou.Ch06.markedPoissonArrivalOutsideIndependenceMany
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
      2 ≤ m →
      (∀ i, MeasurableSet (B i) ∧ B i ⊆ Aᶜ ∧ n (B i) < ⊤) →
        P {omega | (t : WithTop NNReal) < sigma omega ∧
          (∀ i : Fin m, N omega (times i) (B i) = counts i)} =
          P {omega | (t : WithTop NNReal) < sigma omega} *
            P {omega |
              ∀ i : Fin m, N omega (times i) (B i) = counts i}) := by sorry
