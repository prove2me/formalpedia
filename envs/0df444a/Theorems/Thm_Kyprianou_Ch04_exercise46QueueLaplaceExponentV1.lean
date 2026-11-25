-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46QueueLaplaceExponentV1
-- name    : Kyprianou.Ch04.exercise46QueueLaplaceExponentV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T18:21:01.652562+00:00
-- url     : https://prove2.me/theorems/9dabed11-39f9-54cc-a3f9-cb4c01417096
-- title:
--   M/G/1 queue Laplace exponent under unit drift
-- statement:
--   With negative service-mark Lévy measure and unit drift, the queue exponent equals theta minus the arrival intensity times the service exponential deficit integral.
-- source:
--   Kyprianou (2006), Exercise 4.6(i).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46QueueLaplaceExponentV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P G)
    (hBV : L.BoundedVariation) (hDrift : L.drift = 1)
    (lambda : Real) (hlambda : 0 < lambda)
    (service : Measure Real) [IsProbabilityMeasure service]
    (hInputLaw : L.ν = ENNReal.ofReal lambda • service.map (fun x : Real => -x))
    (theta : Real) (htheta : 0 ≤ theta) :
    L.ψ theta = theta - lambda *
      (∫ y : Real, (1 - Real.exp (-theta * y)) ∂service) := by
  sorry
