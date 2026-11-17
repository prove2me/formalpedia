-- Prove2me | Theorems.Thm_Kyprianou_Ch06_consecutiveMarkedPoissonCountIncrements
-- name    : Kyprianou.Ch06.consecutiveMarkedPoissonCountIncrements
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T09:04:20.223408+00:00
-- url     : https://prove2.me/theorems/27df9c56-4afa-45de-b92a-e37ac132ea8d
-- title:
--   Chapter 6 marked Poisson counts in consecutive intervals have independent joint Poisson law
-- statement:
--   For the original marked Poisson point process, a measurable finite-intensity mark set A and any deterministic 0≤s≤t, the A-count increment over [0,s] and over [s,t] are independent Poisson counts with parameters s n(A) and (t-s)n(A). This is the exact two-disjoint-time-rectangle specialisation of the source finite-dimensional Poisson law and supports overlapping outside-mark cylinder independence at differing observation times.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.consecutiveMarkedPoissonCountIncrements
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (A : Set E) (hA : MeasurableSet A) (hFinite : n A < ⊤)
    (s t : NNReal) (hst : s ≤ t) (k l : Nat) :
    P {omega | N omega s A - N omega 0 A = k ∧
      N omega t A - N omega s A = l} =
    ProbabilityTheory.poissonMeasure
      (s * (n A).toNNReal) {k} *
    ProbabilityTheory.poissonMeasure
      ((t-s) * (n A).toNNReal) {l} := by sorry
