-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weighted_simplex_region_map
-- name    : OAI.PiExponent.DeterminantContradiction.weighted_simplex_region_map
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T03:17:02.971519+00:00
-- url     : https://prove2.me/theorems/7bdd879b-3383-4ad7-bf54-9633fda9fdc4
-- title:
--   Diagonal image of the weighted simplex region
-- statement:
--   The coordinatewise map multiplying coordinate i by its positive weight maps the weighted simplex region onto the ordinary simplex.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_WeightedSimplexRegion

open scoped BigOperators Topology
open OAI.PiExponent.DeterminantContradiction

theorem OAI.PiExponent.DeterminantContradiction.weighted_simplex_region_map (m : ℕ) (w : Fin m → ℝ) (T : ℝ) (hw : ∀ i, 0 < w i) : (fun x i => w i * x i) '' weightedSimplexRegion w T = {x : Fin m → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, x i ≤ T} := by sorry
