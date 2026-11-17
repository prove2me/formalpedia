-- Prove2me | Theorems.Thm_Kyprianou_Ch06_firstArrivalIndependentOfRepeatedOutsideCount
-- name    : Kyprianou.Ch06.firstArrivalIndependentOfRepeatedOutsideCount
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T08:55:20.428207+00:00
-- url     : https://prove2.me/theorems/4fe7aecb-135f-4a5d-ad51-68e4fb84c45c
-- title:
--   Chapter 6 first A-arrival independent of two repeated observations of the same outside mark count
-- statement:
--   For any original marked Poisson model and one disjoint outside-A measurable finite-intensity mark set B at a deterministic time u, the joint cylinder N_u(B)=k and N_u(B)=l is independent of first A-arrival survival after t. If k=l this reduces to the already Proved singleton count independence. Otherwise the cylinder is empty. This source-faithful theorem handles an exact degenerate overlapping two-coordinate subcase.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.firstArrivalIndependentOfRepeatedOutsideCount
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
        0 < N omega (sigma.untopD 0) {x}))
    (B : Set E) (hB : MeasurableSet B)
    (hAB : Disjoint A B) (hFiniteB : n B < ⊤) :
    let sigma : Omega → WithTop NNReal := fun omega =>
      sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
        {v : NNReal | 0 < v ∧ 0 < N omega v A})
    ∀ (t u : NNReal) (k l : Nat),
      P {omega | (t : WithTop NNReal) < sigma omega ∧ N omega u B = k ∧ N omega u B = l} =
      P {omega | (t : WithTop NNReal) < sigma omega} *
        P {omega | N omega u B = k ∧ N omega u B = l}
 := by sorry
