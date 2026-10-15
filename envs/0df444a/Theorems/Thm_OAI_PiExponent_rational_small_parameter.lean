-- Prove2me | Theorems.Thm_OAI_PiExponent_rational_small_parameter
-- name    : OAI.PiExponent.rational_small_parameter
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-14T22:50:38.295283+00:00
-- url     : https://prove2.me/theorems/f6bddb0f-45b0-49ae-9bfe-86c07b18b918
-- title:
--   A positive rational parameter below an explicit bound
-- statement:
--   For every real nu greater than two, there is a positive rational q below both 1/4 and 3(nu−2)/(4(nu−1)). Both upper bounds are positive under the stated hypothesis, so rational density provides such a q.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PiExponent.lean

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Order

theorem OAI.PiExponent.rational_small_parameter (nu : ℝ) (hnu : 2 < nu) :
    ∃ q : ℚ,
      0 < (q : ℝ) ∧
      (q : ℝ) < min (1 / 4 : ℝ) (3 * (nu - 2) / (4 * (nu - 1))) := by sorry
