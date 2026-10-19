-- Prove2me | Theorems.Thm_OAI_PiExponent_rational_scale_error_control_rational_w
-- name    : OAI.PiExponent.rational_scale_error_control_rational_w
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-15T04:59:08.959302+00:00
-- url     : https://prove2.me/theorems/a3f2d508-b934-4a3f-9ed4-1534132bcf3e
-- title:
--   Choose a compatible rational scale for the geometric weight
-- statement:
--   Given the balance condition and a positive rational v, choose a positive rational w whose ratio to v makes the geometric product less than one and whose reciprocal contribution is bounded by 2s/v.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PiExponent.lean

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Order

theorem OAI.PiExponent.rational_scale_error_control_rational_w
    (theta : ℚ) (m K : ℕ) (v : ℚ) (s : ℝ)
    (hK : 0 < K) (htheta : 0 < theta)
    (hbalance : (K : ℝ) ^ 2 * (theta : ℝ) ^ m < 1)
    (hv : 0 < v) (hs : 0 < s) :
    ∃ w : ℚ, 0 < w ∧
      (K : ℚ) * (w / v) * theta ^ m < 1 ∧
      s * (K : ℝ) / (w : ℝ) < 2 * s / (v : ℝ) := by sorry
