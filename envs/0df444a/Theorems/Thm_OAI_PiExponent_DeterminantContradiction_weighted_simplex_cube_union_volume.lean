-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weighted_simplex_cube_union_volume
-- name    : OAI.PiExponent.DeterminantContradiction.weighted_simplex_cube_union_volume
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T02:59:48.501735+00:00
-- url     : https://prove2.me/theorems/ee9c7bf6-58b0-4c0c-8487-55f14316780a
-- title:
--   Volume of the admissible unit cube union
-- statement:
--   The union of half-open unit cubes based at a finite set of natural-number vectors has volume equal to the cardinality of that set.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Definitions.Def_OAI_NumberTheory_PiExponent_WeightedSimplexRegion

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic

theorem OAI.PiExponent.DeterminantContradiction.weighted_simplex_cube_union_volume
    (m : ℕ) (w : Fin m → ℝ) (T : ℝ) :
    MeasureTheory.volume {x : Fin m → ℝ | ∃ a ∈ OAI.PiExponent.realWeightedSimplex w T, ∀ i, (a i : ℝ) ≤ x i ∧ x i < (a i : ℝ) + 1} =
      ((OAI.PiExponent.realWeightedSimplex w T).card : ENNReal) := by sorry
