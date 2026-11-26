-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45FullSquareEnergyV2
-- name    : Kyprianou.Ch04.exercise45FullSquareEnergyV2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T17:17:36.018576+00:00
-- url     : https://prove2.me/theorems/729b24c3-3321-4bd7-aaa1-be2fcc576056
-- title:
--   exercise45FullSquareEnergyV2
-- statement:
--   exercise45FullSquareEnergyV2
-- source:
--   Exercise 4.5(iii), pure-jump Ito limit

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
open MeasureTheory ProbabilityTheory Filter Set Topology LevyStochCalc.Poisson
open scoped NNReal ENNReal Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise45FullSquareEnergyV2
    (μ : Measure (ℝ × ℝ))
    (h : Integrable (fun z : ℝ × ℝ => min (1 : ℝ) (z.2^2)) μ)
    (hlarge : Integrable (fun z : ℝ × ℝ => z.2^2)
      (μ.restrict {z : ℝ × ℝ | 1/2 < |z.2|})) :
    Integrable (fun z : ℝ × ℝ => z.2^2) μ := by
  sorry
