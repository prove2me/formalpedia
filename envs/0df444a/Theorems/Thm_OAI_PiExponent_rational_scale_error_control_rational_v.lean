-- Prove2me | Theorems.Thm_OAI_PiExponent_rational_scale_error_control_rational_v
-- name    : OAI.PiExponent.rational_scale_error_control_rational_v
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-15T04:58:53.235977+00:00
-- url     : https://prove2.me/theorems/a53a3757-5ddb-4e75-af63-ed68a216711f
-- title:
--   Choose a rational scale controlling the fixed reciprocal errors and collision bound
-- statement:
--   Under the capacity bound, choose a positive rational v so that the combined fixed reciprocal-error coefficient contributes less than g/2 and the collision threshold c/v remains strictly above 1+g.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PiExponent.lean

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Order

theorem OAI.PiExponent.rational_scale_error_control_rational_v
    (b s g c : ℝ) (hb : 0 ≤ b) (hs : 0 < s) (hg : 0 < g)
    (hcapacity : 4 * (b + 2 * s) * (1 + g) / g < c) :
    ∃ v : ℚ, 0 < v ∧ (b + 2 * s) / (v : ℝ) < g / 2 ∧
      1 + g < c / (v : ℝ) := by sorry
