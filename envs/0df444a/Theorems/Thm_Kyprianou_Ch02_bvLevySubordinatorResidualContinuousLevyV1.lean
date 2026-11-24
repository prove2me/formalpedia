-- Prove2me | Theorems.Thm_Kyprianou_Ch02_bvLevySubordinatorResidualContinuousLevyV1
-- name    : Kyprianou.Ch02.bvLevySubordinatorResidualContinuousLevyV1
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T22:33:43.175631+00:00
-- url     : https://prove2.me/theorems/e8ea1048-41b4-428f-a856-ce86acc89e9a
-- title:
--   Jump residual of a Lévy subordinator is continuous monotone Lévy
-- statement:
--   Let $Y$ be a real Lévy process with almost surely monotone paths. Write $J_t$ for the cumulative sum of its positive jumps and set $C_t=Y_t-J_t$. Then $C$ is itself a Lévy process, almost every path of $C$ is continuous and monotone, and the pathwise identity $Y=C+J$ holds almost surely.
-- source:
--   Kyprianou (2006), Ch.2, Lemma 2.12 / Exercise 2.8

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.bvLevySubordinatorResidualContinuousLevyV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : ℝ≥0 → Ω → ℝ)
    (hY : ProbabilityTheory.IsLevyProcess Y P)
    (hMono : ∀ᵐ ω ∂P, Monotone (fun t => Y t ω)) :
    let J : ℝ≥0 → Ω → ℝ := fun t ω =>
      ∑' s : Set.Ioc (0 : ℝ≥0) t,
        max (Y s.1 ω -
          Filter.limUnder (nhdsWithin s.1 (Set.Iio s.1)) (fun u => Y u ω)) 0
    let C : ℝ≥0 → Ω → ℝ := fun t ω => Y t ω - J t ω
    ProbabilityTheory.IsLevyProcess C P ∧
      (∀ᵐ ω ∂P, Continuous (fun t => C t ω)) ∧
      (∀ᵐ ω ∂P, Monotone (fun t => C t ω)) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, Y t ω = C t ω + J t ω) := by sorry
