-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_strict_weighted_simplex_card_asymptotic
-- name    : OAI.PiExponent.DeterminantContradiction.strict_weighted_simplex_card_asymptotic
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T23:15:17.020416+00:00
-- url     : https://prove2.me/theorems/6e2834c8-7ed9-4e02-9c06-ae3f5ac7cb53
-- title:
--   Asymptotic count of a strict weighted simplex
-- statement:
--   For positive real weights in any finite dimension, the number of natural-number lattice points whose weighted sum is strictly below H, divided by H to the dimension, converges to the reciprocal of the factorial times the product of the weights. The zero-dimensional boundary case also holds: the simplex has one point for H > 0 and the stated coefficient is 1.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_SimplexCounting_WeightedDomains
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators Topology
open Filter

theorem OAI.PiExponent.DeterminantContradiction.strict_weighted_simplex_card_asymptotic
    (n : ℕ) (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) :
    Tendsto
      (fun H : ℝ => ((OAI.PiExponent.strictWeightedSimplex w H).card : ℝ) / H ^ n)
      atTop
      (𝓝 (1 / ((Nat.factorial n : ℝ) * ∏ i, w i))) := by sorry
