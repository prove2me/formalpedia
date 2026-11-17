-- Prove2me | Theorems.Thm_Kyprianou_Ch06_firstArrivalIndependentOfTwoOverlappingOutsideCountsSameTime
-- name    : Kyprianou.Ch06.firstArrivalIndependentOfTwoOverlappingOutsideCountsSameTime
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T12:20:47.539381+00:00
-- url     : https://prove2.me/theorems/be9feb0e-f5ce-4323-873d-a47fa38bcf8c
-- title:
--   Chapter 6 first A-arrival independent of two overlapping outside mark counts observed at common time
-- statement:
--   For the original Chapter 6 marked-Poisson counting process and first-A-mark selector, first A-arrival survival after t is independent of the joint count cylinder N_u(B)=k and N_u(C)=l for any two measurable finite-intensity outside-A mark sets B,C and arbitrary count levels, even when B and C overlap spatially, at a common observation time u. First factor the corresponding zero A-count joint event using a source-faithful disjoint-spatial-atom decomposition of overlapping marks and the original Poisson rectangular law. The independently proved exponential zero-count marginal implies continuous joint probability, allowing the Proved first-arrival joint-event sandwich to transfer the zero-count factorisation to first-arrival survival. Retains all original hypotheses, including zero A-intensity.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter Topology
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.firstArrivalIndependentOfTwoOverlappingOutsideCountsSameTime
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (n : Measure E) (N : Omega → NNReal → Set E → Nat)
    (A : Set E) (firstMark : Omega → Option E)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (hA : MeasurableSet A) (hFA : n A < ⊤)
    (hMark : ∀ᵐ omega ∂P,
      let sigma : WithTop NNReal :=
        sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
          {v : NNReal | 0 < v ∧ 0 < N omega v A})
      (sigma = ⊤ → firstMark omega = none) ∧
      (sigma ≠ ⊤ → ∃ x : E,
        firstMark omega = some x ∧ x ∈ A ∧
        0 < N omega (sigma.untopD 0) {x}))
    (B C : Set E) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hFB : n B < ⊤) (hFC : n C < ⊤)
    (t u : NNReal) (k l : Nat) :
    P {omega | (t : WithTop NNReal) <
        sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
          {v : NNReal | 0 < v ∧ 0 < N omega v A}) ∧
      N omega u B = k ∧ N omega u C = l} =
    P {omega | (t : WithTop NNReal) <
        sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
          {v : NNReal | 0 < v ∧ 0 < N omega v A})} *
    P {omega | N omega u B = k ∧ N omega u C = l} := by sorry
