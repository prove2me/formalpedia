-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_normalized_simplex_power_integral
-- name    : OAI.PiExponent.DeterminantContradiction.normalized_simplex_power_integral
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T09:46:29.9254+00:00
-- url     : https://prove2.me/theorems/59bc43af-81ca-410e-ad7d-daad9030c901
-- title:
--   Integral of a normalized power
-- statement:
--   For nonnegative U, the interval integral of (U-t)^m divided by m factorial from zero to U equals U^(m+1) divided by (m+1) factorial.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib

theorem OAI.PiExponent.DeterminantContradiction.normalized_simplex_power_integral (m : ℕ) (U : ℝ) (hU : 0 ≤ U) :
    ∫ t in (0 : ℝ)..U, (U - t) ^ m / (Nat.factorial m : ℝ) =
      (U ^ (m + 1)) / (Nat.factorial (m + 1) : ℝ) := by sorry
