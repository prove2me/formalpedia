-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_finite_negative_jump_transforms
-- name    : Kyprianou.Ch08.StageB.source_result81_finite_negative_jump_transforms
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T20:51:07.356669+00:00
-- url     : https://prove2.me/theorems/41ddaf77-2525-482a-8643-db0a0bb961c5
-- title:
--   Uncompensated finite negative jump law and its two transforms
-- statement:
--   For a finite negative jump measure, a compound-Poisson probability law realizes both uncompensated jump exponents. The two centered kernels are integrable for the original measure.
-- source:
--   Finite-activity construction in the Lévy-Khintchine cutoff argument for Kyprianou (2006), Ch. 8, Theorem 8.1. Parent Prove2Me theorem d6b08b21-0232-4da0-9092-8b64ae06523d.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.source_result81_finite_negative_jump_transforms
    (ν : Measure ℝ) [IsFiniteMeasure ν] (hneg : ν (Ici (0 : ℝ)) = 0)
    (t : ℝ≥0) :
    ∃ μ : ProbabilityMeasure ℝ,
      (∀ ξ : ℝ, Integrable (fun y : ℝ => Complex.exp ((ξ : ℂ) * y * Complex.I) - 1) ν ∧
        charFun (μ : Measure ℝ) ξ = Complex.exp (((t : ℝ) : ℂ) *
          ∫ y : ℝ, (Complex.exp ((ξ : ℂ) * y * Complex.I) - 1) ∂ν)) ∧
      (∀ β : ℝ, 0 ≤ β → Integrable (fun y => Real.exp (β * y) - 1) ν ∧
        Integrable (fun x => Real.exp (β * x)) (μ : Measure ℝ) ∧
        (∫ x, Real.exp (β * x) ∂(μ : Measure ℝ)) =
          Real.exp ((t : ℝ) * ∫ y, (Real.exp (β * y) - 1) ∂ν)) := by
  sorry
