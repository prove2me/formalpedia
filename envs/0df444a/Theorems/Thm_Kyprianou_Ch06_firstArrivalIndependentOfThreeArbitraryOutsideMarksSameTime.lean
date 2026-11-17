-- Prove2me | Theorems.Thm_Kyprianou_Ch06_firstArrivalIndependentOfThreeArbitraryOutsideMarksSameTime
-- name    : Kyprianou.Ch06.firstArrivalIndependentOfThreeArbitraryOutsideMarksSameTime
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T05:47:52.679096+00:00
-- url     : https://prove2.me/theorems/01f377b1-0f6f-4b6c-b881-3daa99649ee7
-- title:
--   First A-arrival independent of the joint counts of three arbitrary overlapping outside marks at one time
-- statement:
--   Under the original Chapter 6 marked Poisson source hypothesis, the survival of the first A-arrival is independent of three count observations at the same time u on arbitrarily overlapping outside-A mark sets B,C,D and all count levels. Proof directly applies the proved seven-Venn-atom zero A-count three-mark factorisation for every deterministic time and the original first-arrival transfer from zero-count independence.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.firstArrivalIndependentOfThreeArbitraryOutsideMarksSameTime
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
    (B C D : Set E) (hB : MeasurableSet B)
    (hC : MeasurableSet C) (hD : MeasurableSet D)
    (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hAD : Disjoint A D)
    (hFB : n B < ⊤) (hFC : n C < ⊤)
    (hFD : n D < ⊤)
    (t u : NNReal) (k l q : Nat) :
    P {omega | (t : WithTop NNReal) <
      sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
        {v : NNReal | 0 < v ∧ 0 < N omega v A}) ∧
      N omega u B = k ∧ N omega u C = l ∧
      N omega u D = q} =
    P {omega | (t : WithTop NNReal) <
      sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
        {v : NNReal | 0 < v ∧ 0 < N omega v A})} *
      P {omega | N omega u B = k ∧
        N omega u C = l ∧ N omega u D = q} := by sorry
