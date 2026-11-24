-- Prove2me | Theorems.Thm_Kyprianou_Ch03_stableHighGridExpectationTendstoZeroV1
-- name    : Kyprianou.Ch03.stableHighGridExpectationTendstoZeroV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T18:24:14.567997+00:00
-- url     : https://prove2.me/theorems/b41e9f49-2e80-4ff7-b697-4977eab087bf
-- title:
--   Stable uniform-grid absolute increments have vanishing exponential expectations
-- statement:
--   The uniform grid consists of iid increments distributed as a scaled unit-time variable. Its Laplace expectation is bounded by exp(-c(n+1)^(1-1/α)), which vanishes for α>1.
-- source:
--   Auxiliary limit for Kyprianou (2006), Exercise 3.7.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

theorem Kyprianou.Ch03.stableHighGridExpectationTendstoZeroV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : NNReal → Ω → ℝ) (hX : ProbabilityTheory.IsLevyProcess X P)
    (α : ℝ) (hα : 1 < α) (hne : ¬ X 1 =ᵐ[P] 0)
    (hStable : ∀ (t : NNReal) (scale : ℝ), 0 < scale →
      P.map (X (t * Real.toNNReal scale)) =
        P.map (fun w => scale ^ (1 / α) * X t w)) :
    Tendsto (fun n : ℕ => ∫ w, Real.exp (-(∑ i : Fin (n + 1),
          |X (((i.val + 1 : ℕ) : NNReal) * (((n : NNReal) + 1)⁻¹)) w -
           X ((i.val : NNReal) * (((n : NNReal) + 1)⁻¹)) w|)) ∂P)
      atTop (𝓝 0) := by sorry
