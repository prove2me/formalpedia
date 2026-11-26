-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46FiniteArrivalIntensityV1
-- name    : Kyprianou.Ch04.exercise46FiniteArrivalIntensityV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T22:56:04.482247+00:00
-- url     : https://prove2.me/theorems/40d788af-2651-5a8b-bdde-bf2c034a599e
-- title:
--   Finite arrival intensity from positive service law
-- statement:
--   Reflect the positive service law to negative jump marks; its mass is one.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical Set
open scoped NNReal ENNReal
set_option autoImplicit false
open scoped Topology

theorem Kyprianou.Ch04.exercise46FiniteArrivalIntensityV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G)
    (lambda : Real) (hlambda : 0 < lambda)
    (service : Measure Real) [IsProbabilityMeasure service]
    (hServicePositive : service (Ioi (0 : Real)) = 1)
    (hInputLaw : L.ν = ENNReal.ofReal lambda • service.map (fun x : Real => -x)) :
    L.ν (Iio (0 : Real)) = ENNReal.ofReal lambda := by
  sorry
