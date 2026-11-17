-- Prove2me | Theorems.Thm_Kyprianou_Ch06_markedPoissonMarginalCountLaw
-- name    : Kyprianou.Ch06.markedPoissonMarginalCountLaw
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T07:41:26.598981+00:00
-- url     : https://prove2.me/theorems/f6a2a1b3-ca71-4ba2-932d-12c816f1e567
-- title:
--   Chapter 6 marked Poisson point process: marginal count Poisson distribution
-- statement:
--   For the original Chapter 6 marked Poisson point process, every finite-intensity measurable mark set has at each deterministic time the Poisson marginal count distribution, deduced from the independent rectangular increments and almost-sure zero initial counts.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.markedPoissonMarginalCountLaw
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (t : NNReal) (A : Set E) (hA : MeasurableSet A)
    (hFinite : n A < ⊤) (k : Nat) :
  P {omega | N omega t A = k} =
    ProbabilityTheory.poissonMeasure (t * (n A).toNNReal) {k} := by sorry
