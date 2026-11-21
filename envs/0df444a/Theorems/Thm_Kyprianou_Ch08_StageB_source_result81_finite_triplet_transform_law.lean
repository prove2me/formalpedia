-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_finite_triplet_transform_law
-- name    : Kyprianou.Ch08.StageB.source_result81_finite_triplet_transform_law
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T20:23:24.156288+00:00
-- url     : https://prove2.me/theorems/d6b08b21-0232-4da0-9092-8b64ae06523d
-- title:
--   Characteristic and nonnegative real transforms of a finite negative triplet
-- statement:
--   A Gaussian convolved with a compensated compound-Poisson law for a finite negative jump measure gives the characteristic and positive real Lévy–Khintchine transforms with the strict small-jump truncation.
-- source:
--   Finite Lévy–Khintchine cutoff argument for Kyprianou (2006), Chapter 8, Theorem 8.1. Parent Prove2Me theorem 987aeaac-dbe6-4ff6-aca6-d87cd87bffde.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory ProbabilityTheory Filter Set Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.source_result81_finite_triplet_transform_law
    (ν : Measure ℝ) [IsFiniteMeasure ν] (hneg : ν (Ici (0 : ℝ)) = 0)
    (b σ : ℝ) (v t : ℝ≥0) (hσ : σ ^ 2 = (v : ℝ)) :
    ∃ μ : ProbabilityMeasure ℝ,
      (∀ ξ : ℝ, charFun (μ : Measure ℝ) ξ =
        Complex.exp (((t : ℝ) : ℂ) * (Complex.I * ((b * ξ : ℝ) : ℂ) -
          (((v : ℝ) * ξ ^ 2 / 2 : ℝ) : ℂ) + ∫ y, levyCompensatedIntegrand ξ y ∂ν))) ∧
      (∀ β : ℝ, 0 ≤ β →
        Integrable (fun x => Real.exp (β * x)) (μ : Measure ℝ) ∧
        (∫ x, Real.exp (β * x) ∂(μ : Measure ℝ)) =
          Real.exp ((t : ℝ) * tripletLaplace (-b) σ ν β)) := by
  sorry
