-- Prove2me | Theorems.Thm_Kyprianou_Ch06_firstArrivalIndependentOfOneDisjointCount
-- name    : Kyprianou.Ch06.firstArrivalIndependentOfOneDisjointCount
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T08:26:48.988731+00:00
-- url     : https://prove2.me/theorems/ce35f367-9a3c-43ce-895c-7d3e24f9097c
-- title:
--   Chapter 6 first Poisson mark arrival independent of one outside-mark count
-- statement:
--   Under the complete original Chapter 6 marked Poisson hypotheses, let A and B be disjoint measurable finite-intensity mark sets. At arbitrary deterministic times t,u, the survival event of the first positive A-count arrival after t is independent of the point-count event N_u(B)=k for every natural k. The proof uses source-faithful first-arrival survival and continuous sandwich laws, genuine spatial independence of marked Poisson counts and exact Poisson marginal distribution.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.firstArrivalIndependentOfOneDisjointCount
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
        0 < N omega (sigma.untopD 0) {x}))    (B : Set E) (hB : MeasurableSet B)
    (hAB : Disjoint A B) (hFiniteB : n B < ⊤) :
    let sigma : Omega → WithTop NNReal := fun omega =>
      sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
        {v : NNReal | 0 < v ∧ 0 < N omega v A})
    ∀ (t u : NNReal) (k : Nat),
      P {omega | (t : WithTop NNReal) < sigma omega ∧ N omega u B = k} =
      P {omega | (t : WithTop NNReal) < sigma omega} *
        P {omega | N omega u B = k}
 := by sorry
