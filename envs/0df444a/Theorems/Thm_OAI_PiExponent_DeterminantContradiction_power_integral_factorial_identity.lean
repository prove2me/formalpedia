-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_power_integral_factorial_identity
-- name    : OAI.PiExponent.DeterminantContradiction.power_integral_factorial_identity
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T21:51:22.897023+00:00
-- url     : https://prove2.me/theorems/e82c788f-5bab-4d57-b16c-c7b05539ac2b
-- title:
--   Power integral and factorial identity
-- statement:
--   For every natural exponent and real endpoint, the oriented integral of the power of the distance to the endpoint, multiplied by the unit simplex volume, equals the radius power divided by the successor factorial.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.power_integral_factorial_identity
    (n : ℕ) (r : ℝ) :
    r ^ (n + 1) / (Nat.factorial (n + 1) : ℝ) =
      ((1 : ℝ) ^ n / (Nat.factorial n : ℝ)) *
        (∫ t in (0 : ℝ)..r, (r - t) ^ n) := by sorry
