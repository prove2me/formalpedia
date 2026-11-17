-- Prove2me | Theorems.Thm_Kyprianou_Ch06_markedPoissonFirstArrivalSurvivalAndRestriction
-- name    : Kyprianou.Ch06.markedPoissonFirstArrivalSurvivalAndRestriction
-- status  : Open
-- author  : @WillR
-- created : 2026-11-16T07:36:11.898054+00:00
-- url     : https://prove2.me/theorems/18484b47-48b4-49f7-a059-94c7cd2003b2
-- title:
--   Chapter 6 Lemma 6.18 component: arrival survival and restricted-mark independence
-- statement:
--   Under the full original marked Poisson process hypotheses, prove the exponential survival law of the first A-mark and its independence from all finite-dimensional count cylinders outside A.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch06

theorem Kyprianou.Ch06.markedPoissonFirstArrivalSurvivalAndRestriction
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
    (∀ t : NNReal,
      P {omega | (t : WithTop NNReal) < sigma omega} =
        ENNReal.ofReal
          (Real.exp (-((n A).toReal * (t : Real))))) ∧
    (∀ (m : Nat) (times : Fin m → NNReal)
      (B : Fin m → Set E) (counts : Fin m → Nat) (t : NNReal),
      (∀ i, MeasurableSet (B i) ∧ B i ⊆ Aᶜ ∧ n (B i) < ⊤) →
        P {omega | (t : WithTop NNReal) < sigma omega ∧
          (∀ i : Fin m, N omega (times i) (B i) = counts i)} =
          P {omega | (t : WithTop NNReal) < sigma omega} *
            P {omega |
              ∀ i : Fin m, N omega (times i) (B i) = counts i}) := by sorry
