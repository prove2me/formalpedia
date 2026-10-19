-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_weight_mem_strictWeightedSimplex
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.weight_mem_strictWeightedSimplex
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T07:19:36.164897+00:00
-- url     : https://prove2.me/theorems/a68a6572-c5ad-491c-a668-e3aa70c6ce5c
-- title:
--   Positive weighted cutoff bounds every exponent coordinate
-- statement:
--   For positive weights and positive cutoff, an exponent vector whose weighted sum is strictly below the cutoff belongs to the strict weighted simplex. Each coordinate is bounded by the floor of the cutoff divided by its weight, which places it in the finite product used to define the simplex; the assumed strict weighted-sum bound then gives membership in its strict filter.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib
import Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_SimplexCounting_WeightedDomains

open scoped BigOperators

theorem OAI.PiExponent.AdmissibleFormalInterpolation.weight_mem_strictWeightedSimplex
    {m : ℕ} (v0 : ℝ) (u : Fin m → ℝ) (H : ℝ)
    (hv0 : 0 < v0) (hu : ∀ i, 0 < u i) (hH : 0 < H)
    (a : Fin (m + 1) → ℕ)
    (ha : (∑ i, Fin.cases v0 u i * (a i : ℝ)) < H) :
    a ∈ OAI.PiExponent.strictWeightedSimplex (Fin.cases v0 u) H := by sorry
