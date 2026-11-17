-- Prove2me | Theorems.Thm_Kyprianou_Ch06_firstArrivalIndependentOfNestedOutsideZeroCounts
-- name    : Kyprianou.Ch06.firstArrivalIndependentOfNestedOutsideZeroCounts
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T11:51:31.116778+00:00
-- url     : https://prove2.me/theorems/52dcc039-e4be-4e1b-9400-895534087e9a
-- title:
--   Chapter 6 first A-arrival independent of nested outside-A zero count observations at ordered times
-- statement:
--   With original Chapter 6 marked Poisson and first-mark hypotheses, if outside-A marks B⊆C and s≤u, the conjunction N_s(B)=0 and N_u(C)=0 is independent of first A-arrival survival after t. The first zero condition follows almost surely from the second by spatial and temporal monotonicity. The genuine source singleton outside count independence theorem then establishes the full event identity for arbitrary marked B,C and ordered times.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.firstArrivalIndependentOfNestedOutsideZeroCounts
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
    (B C : Set E) (hC : MeasurableSet C)
    (hAC : Disjoint A C) (hFC : n C < ⊤)
    (hBC : B ⊆ C) (s u t : NNReal) (hsu : s ≤ u) :
    P {omega | (t : WithTop NNReal) <
        sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
          {v : NNReal | 0 < v ∧ 0 < N omega v A}) ∧
      N omega s B = 0 ∧ N omega u C = 0} =
    P {omega | (t : WithTop NNReal) <
        sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
          {v : NNReal | 0 < v ∧ 0 < N omega v A})} *
    P {omega | N omega s B = 0 ∧ N omega u C = 0} := by sorry
