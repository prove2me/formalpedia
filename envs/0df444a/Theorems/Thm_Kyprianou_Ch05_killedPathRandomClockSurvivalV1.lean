-- Prove2me | Theorems.Thm_Kyprianou_Ch05_killedPathRandomClockSurvivalV1
-- name    : Kyprianou.Ch05.killedPathRandomClockSurvivalV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T17:19:41.895214+00:00
-- url     : https://prove2.me/theorems/3d13b9b2-635c-454f-ad26-0bc6b484b98b
-- title:
--   Independent exponential killing factors a measurable path-dependent crossing event
-- statement:
--   Map the independent path and death to the product of their laws. The sections of the joint event have measure equal to exponential survival at the path clock, or zero for infinite clocks or excluded paths.
-- source:
--   Kyprianou (2006), Chapter 5, Theorem 5.6.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_LeanLevy_RandomMeasure_PoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory Filter Set Complex Topology Kyprianou.Ch05
open scoped NNReal ENNReal Topology Classical
set_option autoImplicit false

theorem Kyprianou.Ch05.killedPathRandomClockSurvivalV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → ℝ) (death : Omega → WithTop NNReal)
    (eta : ℝ) (hKilled : IsKilledSubordinator P Y death eta)
    (T : (NNReal → ℝ) → ENNReal) (hT : Measurable T)
    (C : Set (NNReal → ℝ)) (hC : MeasurableSet C) :
    P {w | (fun t => Y t w) ∈ C ∧ T (fun t => Y t w) < death w} =
      ∫⁻ f, if f ∈ C ∧ T f ≠ ⊤ then
        ENNReal.ofReal (Real.exp (-eta * (T f).toReal)) else 0
        ∂(P.map (fun w t => Y t w)) := by
  sorry
