-- Prove2me | Theorems.Thm_Kyprianou_Ch06_markedPoissonArrivalOutsideThreeOrMoreOverlapping
-- name    : Kyprianou.Ch06.markedPoissonArrivalOutsideThreeOrMoreOverlapping
-- status  : Open
-- author  : @WillR
-- created : 2026-11-16T09:05:02.360752+00:00
-- url     : https://prove2.me/theorems/e18936a3-8c9f-4bd6-8dc1-38325291ccb8
-- title:
--   Chapter 6 first A-arrival independence of three or more outside mark counts when some mark sets overlap
-- statement:
--   Under the full original Chapter 6 marked Poisson model, prove first A-arrival survival independent of an arbitrary finite outside-A cylinder of at least three count coordinates if at least one pair of outside mark sets overlaps. The complementary case of pairwise spatially disjoint outside sets has a separate exact general finite-dimensional source-faithful proof in progress. This retains all original quantifiers, mark selector, intensity and arbitrary observation times and counts.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch06

theorem Kyprianou.Ch06.markedPoissonArrivalOutsideThreeOrMoreOverlapping
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
      (∀ i, MeasurableSet (B i) ∧ B i ⊆ Aᶜ ∧ n (B i) < ⊤) →
        P {omega | (t : WithTop NNReal) < sigma omega ∧
          (∀ i : Fin m, N omega (times i) (B i) = counts i)} =
          P {omega | (t : WithTop NNReal) < sigma omega} *
            P {omega |
              ∀ i : Fin m, N omega (times i) (B i) = counts i}) := by sorry
