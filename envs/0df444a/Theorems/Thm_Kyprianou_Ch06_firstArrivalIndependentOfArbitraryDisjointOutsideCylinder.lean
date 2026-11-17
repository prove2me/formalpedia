-- Prove2me | Theorems.Thm_Kyprianou_Ch06_firstArrivalIndependentOfArbitraryDisjointOutsideCylinder
-- name    : Kyprianou.Ch06.firstArrivalIndependentOfArbitraryDisjointOutsideCylinder
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T09:00:38.598452+00:00
-- url     : https://prove2.me/theorems/ea2e81d6-d2ef-4502-9b22-f44830fcd975
-- title:
--   Chapter 6 first marked A-arrival independent of arbitrary finite disjoint outside-A count cylinders
-- statement:
--   For any marked Poisson point process as exactly specified in Kyprianou (2006) Chapter 6, any finite family of pairwise spatially disjoint measurable finite-intensity mark sets outside A and arbitrary observation times and count levels, the survival event of first A-arrival after t is independent of the entire finite-dimensional count cylinder. This source-faithful theorem follows from genuine finite-dimensional spatial Poisson independence, the already proved exact A zero-count exponential marginal, its joint continuity, first-arrival joint-event sandwich and the A-arrival survival law; no extra independence is assumed.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter Topology
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.firstArrivalIndependentOfArbitraryDisjointOutsideCylinder
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (n : Measure E) (N : Omega → NNReal → Set E → Nat)
    (A : Set E) (firstMark : Omega → Option E)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (hA : MeasurableSet A) (hFA : n A < ⊤)
    (hMark : ∀ᵐ omega ∂P,
      let sigma : WithTop NNReal :=
        sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
          {t : NNReal | 0 < t ∧ 0 < N omega t A})
      (sigma = ⊤ → firstMark omega = none) ∧
      (sigma ≠ ⊤ → ∃ x : E,
        firstMark omega = some x ∧ x ∈ A ∧
        0 < N omega (sigma.untopD 0) {x}))
    (m : Nat) (times : Fin m → NNReal)
    (B : Fin m → Set E) (counts : Fin m → Nat)
    (hB : ∀ i, MeasurableSet (B i) ∧ B i ⊆ Aᶜ ∧ n (B i) < ⊤)
    (hDisj : ∀ i j : Fin m, i ≠ j → Disjoint (B i) (B j))
    (t : NNReal) :
    P {omega |
      (t : WithTop NNReal) <
        sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
          {u : NNReal | 0 < u ∧ 0 < N omega u A}) ∧
      ∀ i : Fin m, N omega (times i) (B i) = counts i} =
    P {omega |
      (t : WithTop NNReal) <
        sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
          {u : NNReal | 0 < u ∧ 0 < N omega u A})} *
    P {omega | ∀ i : Fin m, N omega (times i) (B i) = counts i} := by sorry
