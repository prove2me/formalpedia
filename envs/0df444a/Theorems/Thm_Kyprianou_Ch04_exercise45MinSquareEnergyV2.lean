-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45MinSquareEnergyV2
-- name    : Kyprianou.Ch04.exercise45MinSquareEnergyV2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T17:10:01.332809+00:00
-- url     : https://prove2.me/theorems/9304054b-91e4-4cee-b9d6-44eb1fc63aae
-- title:
--   exercise45MinSquareEnergyV2
-- statement:
--   exercise45MinSquareEnergyV2
-- source:
--   Exercise 4.5(iii), pure-jump Ito limit

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
open MeasureTheory ProbabilityTheory Filter Set Topology LevyStochCalc.Poisson
open scoped NNReal ENNReal Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise45MinSquareEnergyV2
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν] (hν : IsLevyMeasure ν)
    (N : PoissonRandomMeasure.{0,0,0} P ν) :
    ∀ᵐ w ∂P, ∀ T : NNReal,
      Integrable (fun z : ℝ × ℝ => min (1 : ℝ) (z.2^2))
        ((N.N w).restrict (Ioc (0 : ℝ) (T : ℝ) ×ˢ Set.univ)) := by
  sorry
