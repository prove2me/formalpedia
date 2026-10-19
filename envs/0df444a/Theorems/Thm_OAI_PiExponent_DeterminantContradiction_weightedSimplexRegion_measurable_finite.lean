-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplexRegion_measurable_finite
-- name    : OAI.PiExponent.DeterminantContradiction.weightedSimplexRegion_measurable_finite
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T03:28:20.811845+00:00
-- url     : https://prove2.me/theorems/405fd6ac-3bb6-435f-a3b6-892c59d85679
-- title:
--   Measurability and finite volume of the weighted simplex region
-- statement:
--   For positive weights and any real cutoff, the weighted simplex region is measurable and has finite volume.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_WeightedSimplexRegion

open scoped BigOperators Topology
open OAI.PiExponent.DeterminantContradiction

theorem OAI.PiExponent.DeterminantContradiction.weightedSimplexRegion_measurable_finite (m : ℕ) (w : Fin m → ℝ) (T : ℝ) (hw : ∀ i, 0 < w i) : MeasurableSet (weightedSimplexRegion w T) ∧ MeasureTheory.volume (weightedSimplexRegion w T) < ⊤ := by sorry
