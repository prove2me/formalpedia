-- Prove2me | Theorems.Thm_OAI_PiExponent_window_lower_ratio_of_scaled_power
-- name    : OAI.PiExponent.window_lower_ratio_of_scaled_power
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-14T09:26:03.652827+00:00
-- url     : https://prove2.me/theorems/2151fabc-a4e5-493e-8d75-4ce85b45633b
-- title:
--   Scaled power lower bound implies the quotient inequality
-- statement:
--   For positive theta and A, the strict bound (RA/theta)^m/8 < K implies the desired quotient inequality. It holds for every real R and all natural m and K, including m = 0.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PiExponent.lean

import Mathlib.Data.Real.Basic

theorem OAI.PiExponent.window_lower_ratio_of_scaled_power
    (theta A R : ℝ) (m K : ℕ)
    (htheta : 0 < theta) (hA : 0 < A)
    (hscaled : (R * A / theta) ^ m / 8 < (K : ℝ)) :
    R ^ m / (8 * ((m : ℝ) + 1)) <
      ((K : ℝ) * theta ^ m) / (((m : ℝ) + 1) * A ^ m) := by sorry
