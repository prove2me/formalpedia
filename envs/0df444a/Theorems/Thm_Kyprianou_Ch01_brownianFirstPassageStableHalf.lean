-- Prove2me | Theorems.Thm_Kyprianou_Ch01_brownianFirstPassageStableHalf
-- name    : Kyprianou.Ch01.brownianFirstPassageStableHalf
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T08:21:26.265421+00:00
-- url     : https://prove2.me/theorems/e9e55aff-e4f0-41b9-b882-19bac06e1cc9
-- title:
--   Exercise 1.7: Brownian first-passage stable half-subordinator transform
-- statement:
--   Exercise 1.7: for standard driftless Brownian motion the first passage to level s>0 has Laplace transform exp(−s√(2q)), characteristic of a strictly 1/2-stable ascending passage subordinator. The stronger independent-increment process and stable Lévy triplet conditions remain separate subgoals; this target alone is the nontrivial transform calculation. Draft not remotely elaborated.
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.7, printed p. 29.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.brownianFirstPassageStableHalf
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ)
    (hB : IsLinearBrownian P B 1 0)
    (hmeas : ∀ t : ℝ≥0, Measurable (B t)) :
    ∀ (s q : ℝ), 0 < s → 0 ≤ q →
      Integrable (passageLaplace (firstUpperPassage B s) q) P ∧
      (∫ ω, passageLaplace (firstUpperPassage B s) q ω ∂P) =
        Real.exp (-s * Real.sqrt (2 * q)) := by
  sorry
