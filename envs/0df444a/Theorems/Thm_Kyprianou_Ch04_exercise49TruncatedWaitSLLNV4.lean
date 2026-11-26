-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49TruncatedWaitSLLNV4
-- name    : Kyprianou.Ch04.exercise49TruncatedWaitSLLNV4
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T16:01:48.848335+00:00
-- url     : https://prove2.me/theorems/0f30934a-878a-5ffc-8c5d-8f3a4068f8ef
-- title:
--   exercise49TruncatedWaitSLLNV4
-- statement:
--   exercise49TruncatedWaitSLLNV4
-- source:
--   Exercise 4.9(iii) admissible model construction

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Classical Topology
variable {Ω : Type} [MeasurableSpace Ω]

theorem Kyprianou.Ch04.exercise49TruncatedWaitSLLNV4 (P : Measure Ω) [IsProbabilityMeasure P] (τ : ℕ → Ω → ℝ)
    (hm : ∀ n, Measurable (τ n)) (hi : iIndepFun τ P)
    (hl : ∀ n, IdentDistrib (τ n) (τ 0) P P)
    (hp : ∀ᵐ w ∂P, ∀ n, 0 < τ n w) :
    ∃ c : ℝ, 0 < c ∧ ∀ᵐ w ∂P, ∃ N : ℕ, ∀ n ≥ N,
      c * (n : ℝ) ≤ ∑ i ∈ Finset.range n, τ i w := by sorry
