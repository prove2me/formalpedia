-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_finite_compensator_shift
-- name    : Kyprianou.Ch08.StageB.source_result81_finite_compensator_shift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T08:02:52.819084+00:00
-- url     : https://prove2.me/theorems/bd497495-9923-45fd-b5d9-6b3688fd1bfe
-- title:
--   Finite negative jump compensation in the two transform kernels
-- statement:
--   For a finite negative jump measure, compensation subtracts the retained first moment times the corresponding transform argument. The same real first moment supplies the characteristic and Laplace drift corrections.
-- source:
--   Finite-activity construction in the Lévy–Khintchine cutoff argument for Kyprianou (2006), Ch. 8, Theorem 8.1. Parent Prove2Me theorem d6b08b21-0232-4da0-9092-8b64ae06523d.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.source_result81_finite_compensator_shift
    (ν : Measure ℝ) [IsFiniteMeasure ν] (hneg : ν (Ici (0 : ℝ)) = 0) :
    let C := ∫ y, (Ioo (-1 : ℝ) 0).indicator id y ∂ν
    (∀ ξ : ℝ, Integrable (fun y : ℝ => Complex.exp ((ξ : ℂ) * y * Complex.I) - 1) ν →
      (∫ y, levyCompensatedIntegrand ξ y ∂ν) =
        (∫ y : ℝ, (Complex.exp ((ξ : ℂ) * y * Complex.I) - 1) ∂ν) -
          ((ξ : ℂ) * Complex.I) * (C : ℂ)) ∧
    (∀ β : ℝ, Integrable (fun y => Real.exp (β * y) - 1) ν →
      (∫ y, Real.exp (β * y) - 1 - (if -1 < y then β * y else 0) ∂ν) =
        (∫ y, Real.exp (β * y) - 1 ∂ν) - β * C) := by
  sorry
