-- Prove2me | Theorems.Thm_Kyprianou_Ch06_markedPoissonArrivalOutsideThreeOrMoreBeyondDominatedZeros
-- name    : Kyprianou.Ch06.markedPoissonArrivalOutsideThreeOrMoreBeyondDominatedZeros
-- status  : Open
-- author  : @WillR
-- created : 2026-11-16T12:04:54.367838+00:00
-- url     : https://prove2.me/theorems/c220b7a7-93a7-4a16-8532-ae1a1b759230
-- title:
--   markedPoissonArrivalOutsideThreeOrMoreBeyondDominatedZeros genuine residual Chapter 6 obligation
-- statement:
--   Retains full three-or-more-coordinate overlapping outside-A first-arrival survival independence under original marked-Poisson hypotheses, excluding only all-zero count cylinders in which one mark set and observation time dominate all the others. The excluded case follows from a separate source-exact monotonicity plus singleton outside-mark independence theorem; the child retains genuinely nonzero or nondominated observations, arbitrary mark overlap and times.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch06

theorem Kyprianou.Ch06.markedPoissonArrivalOutsideThreeOrMoreBeyondDominatedZeros
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
      ¬ ((∀ i : Fin m, counts i = 0) ∧
         (∃ u : Fin m, ∀ i : Fin m,
           B i ⊆ B u ∧ times i ≤ times u)) →
      (∀ i, MeasurableSet (B i) ∧ B i ⊆ Aᶜ ∧ n (B i) < ⊤) →
        P {omega | (t : WithTop NNReal) < sigma omega ∧
          (∀ i : Fin m, N omega (times i) (B i) = counts i)} =
          P {omega | (t : WithTop NNReal) < sigma omega} *
            P {omega |
              ∀ i : Fin m, N omega (times i) (B i) = counts i}) := by sorry
