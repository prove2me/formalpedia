-- Prove2me | Theorems.Thm_Kyprianou_Ch06_markedPoissonOneRectangleIncrementLaw
-- name    : Kyprianou.Ch06.markedPoissonOneRectangleIncrementLaw
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T07:34:34.936277+00:00
-- url     : https://prove2.me/theorems/244e0ea0-6f81-4d0b-8418-2c863de1cae5
-- title:
--   Chapter 6 Poisson point process: one rectangular increment law
-- statement:
--   For a published Chapter 6 marked Poisson point process with sigma-finite mark measure n, its count increment over a time interval [s,t], for any measurable finite-intensity mark set A, has the Poisson distribution of parameter (t-s)n(A). This is the one-rectangle consequence of the full finite-rectangle independence hypothesis and is used towards Lemma 6.18.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.markedPoissonOneRectangleIncrementLaw
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (s t : NNReal) (hSt : s ≤ t)
    (A : Set E) (hA : MeasurableSet A) (hFinite : n A < ⊤)
    (k : Nat) :
  P {omega | N omega t A - N omega s A = k} =
    ProbabilityTheory.poissonMeasure ((t - s) * (n A).toNNReal) {k} := by sorry
