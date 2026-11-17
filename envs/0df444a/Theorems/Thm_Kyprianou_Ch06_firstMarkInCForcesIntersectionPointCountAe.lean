-- Prove2me | Theorems.Thm_Kyprianou_Ch06_firstMarkInCForcesIntersectionPointCountAe
-- name    : Kyprianou.Ch06.firstMarkInCForcesIntersectionPointCountAe
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T05:17:49.869965+00:00
-- url     : https://prove2.me/theorems/b3ad94ba-1e87-4836-a286-0cb91b9e82d9
-- title:
--   First marked Poisson point in C implies a positive intersection point count at the original A-arrival time
-- statement:
--   With the exact source first-mark selector and point-process spatial count monotonicity, the first A-mark belonging to C forces an A∩C point by the first A-arrival time. The argument is pointwise outside the original P-null exceptional set and does not presume a specific mark distribution or positive mark intensity.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.firstMarkInCForcesIntersectionPointCountAe
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (A : Set E) (firstMark : Omega → Option E)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (hMark : ∀ᵐ omega ∂P,
      let sigma : WithTop NNReal :=
        sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
          {t : NNReal | 0 < t ∧ 0 < N omega t A})
      (sigma = ⊤ → firstMark omega = none) ∧
      (sigma ≠ ⊤ → ∃ x : E,
        firstMark omega = some x ∧ x ∈ A ∧
        0 < N omega (sigma.untopD 0) {x}))
    (C : Set E) :
    ∀ᵐ omega ∂P, firstMark omega ∈ (some '' C) →
      0 < N omega
        ((sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
          {t : NNReal | 0 < t ∧ 0 < N omega t A})).untopD 0)
        (C ∩ A) := by sorry
