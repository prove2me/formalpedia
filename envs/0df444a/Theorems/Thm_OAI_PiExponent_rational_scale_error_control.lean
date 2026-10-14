-- Prove2me | Theorems.Thm_OAI_PiExponent_rational_scale_error_control
-- name    : OAI.PiExponent.rational_scale_error_control
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-14T08:40:56.176621+00:00
-- url     : https://prove2.me/theorems/768a9938-4a33-49f8-ba9b-f0a7a4a013e1
-- title:
--   Rational scales simultaneously control reciprocal errors and volume
-- statement:
--   For balanced positive centers and a positive rational geometric weight, a nonnegative fixed error a smaller than g/4 and nonnegative reciprocal error coefficients b,d can be controlled using positive rational scales v,w and a positive integer n. If the collision capacity c is strictly larger than 4*(b+2*s)*(1+g)/g, these scales give volume strictly below one, total nonnegative error strictly below g, and collision saving 1+error<c/v.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PiExponent.lean

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Order

theorem OAI.PiExponent.rational_scale_error_control
    (theta : ℚ) (m K : ℕ) (a b s d g c : ℝ)
    (hK : 0 < K) (htheta : 0 < theta)
    (hbalance : (K : ℝ) ^ 2 * (theta : ℝ) ^ m < 1)
    (ha : 0 ≤ a) (ha_gap : a < g / 4)
    (hb : 0 ≤ b) (hs : 0 < s) (hd : 0 ≤ d) (hg : 0 < g)
    (hcapacity : 4 * (b + 2 * s) * (1 + g) / g < c) :
    ∃ (v w : ℚ) (n : ℕ),
      0 < v ∧ 0 < w ∧ 0 < n ∧
      (K : ℚ) * (w / v) * theta ^ m < 1 ∧
      0 ≤ a + b / (v : ℝ) + s * (K : ℝ) / (w : ℝ) + d / (n : ℝ) ∧
      a + b / (v : ℝ) + s * (K : ℝ) / (w : ℝ) + d / (n : ℝ) < g ∧
      1 + (a + b / (v : ℝ) + s * (K : ℝ) / (w : ℝ) + d / (n : ℝ)) <
        c / (v : ℝ) := by sorry
