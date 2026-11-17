-- Prove2me | Theorems.Thm_Kyprianou_Ch06_firstArrivalIndependentOfFiniteOutsideZeroCountsSameTime
-- name    : Kyprianou.Ch06.firstArrivalIndependentOfFiniteOutsideZeroCountsSameTime
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T11:48:42.611205+00:00
-- url     : https://prove2.me/theorems/4751b4d3-055d-4cdc-b591-9599afc89c94
-- title:
--   Chapter 6 first A-arrival independent of any finite simultaneous outside-A zero-count cylinder, including overlapping marks
-- statement:
--   Under the complete original marked-Poisson point process and first-mark selector hypotheses of Kyprianou (2006) Chapter 6, for any finite family of measurable finite-intensity outside-A mark sets, potentially overlapping, and an arbitrary common observation time u, the conjunction that all outside mark counts equal zero is independent of survival of the first A-arrival after t. The source Poisson finite-additivity implies that all counts are zero precisely when the single count on their finite union is zero almost surely; the union remains finite-intensity and outside A, so the independently Proved singleton count independence theorem applies. No additional spatial disjointness or independence hypothesis is introduced.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.firstArrivalIndependentOfFiniteOutsideZeroCountsSameTime
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (n : Measure E) (N : Omega → NNReal → Set E → Nat)
    (A : Set E) (firstMark : Omega → Option E)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (hA : MeasurableSet A) (hFA : n A < ⊤)
    (hMark : ∀ᵐ omega ∂P,
      let sigma : WithTop NNReal :=
        sInf ((fun s : NNReal => (s : WithTop NNReal)) ''
          {s : NNReal | 0 < s ∧ 0 < N omega s A})
      (sigma = ⊤ → firstMark omega = none) ∧
      (sigma ≠ ⊤ → ∃ x : E,
        firstMark omega = some x ∧ x ∈ A ∧
        0 < N omega (sigma.untopD 0) {x}))
    (m : Nat) (B : Fin m → Set E)
    (hB : ∀ i, MeasurableSet (B i) ∧ B i ⊆ Aᶜ ∧ n (B i) < ⊤)
    (t u : NNReal) :
    P {omega | (t : WithTop NNReal) <
        sInf ((fun s : NNReal => (s : WithTop NNReal)) ''
          {s : NNReal | 0 < s ∧ 0 < N omega s A}) ∧
      ∀ i : Fin m, N omega u (B i) = 0} =
    P {omega | (t : WithTop NNReal) <
        sInf ((fun s : NNReal => (s : WithTop NNReal)) ''
          {s : NNReal | 0 < s ∧ 0 < N omega s A})} *
    P {omega | ∀ i : Fin m, N omega u (B i) = 0} := by sorry
