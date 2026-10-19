-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_region_eq_smul_image
-- name    : OAI.PiExponent.DeterminantContradiction.simplex_region_eq_smul_image
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T03:18:37.968618+00:00
-- url     : https://prove2.me/theorems/d9eaa4ff-9ec3-47db-8456-58f3ca60757b
-- title:
--   Simplex region as a scalar image
-- statement:
--   For every nonnegative T, the simplex with coordinate sum at most T is the image of the unit simplex under scalar multiplication by T. This includes T = 0 and m = 0.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib

open scoped BigOperators Topology

theorem OAI.PiExponent.DeterminantContradiction.simplex_region_eq_smul_image
    (m : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    {x : Fin m → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, x i ≤ T} =
      (fun x : Fin m → ℝ => T • x) ''
        {x : Fin m → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, x i ≤ (1 : ℝ)} := by sorry
