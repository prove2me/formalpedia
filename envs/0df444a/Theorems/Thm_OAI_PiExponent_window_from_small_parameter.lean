-- Prove2me | Theorems.Thm_OAI_PiExponent_window_from_small_parameter
-- name    : OAI.PiExponent.window_from_small_parameter
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-14T22:50:45.547385+00:00
-- url     : https://prove2.me/theorems/bb07b3e7-23b6-42c9-a689-8a343247fe6c
-- title:
--   Constructing the window from a small rational parameter
-- statement:
--   Given nu>2 and a positive rational q below the stated bound, the explicit choices theta=(1−q)^2, A=1−q−((nu−2)/(8nu))q, and eta=((nu−2)/(8nu))q satisfy all window inequalities, including strict determinant slack. The q<1/4 bound keeps the parameters in range; the second bound supplies the strict slack.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PiExponent.lean

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Order

theorem OAI.PiExponent.window_from_small_parameter (nu : ℝ) (hnu : 2 < nu)
    (q : ℚ) (hqpos : 0 < (q : ℝ))
    (hqsmall : (q : ℝ) < min (1 / 4 : ℝ) (3 * (nu - 2) / (4 * (nu - 1)))) :
    ∃ (theta : ℚ) (A eta : ℝ),
      theta = (1 - q) ^ 2 ∧
      A = 1 - (q : ℝ) - ((nu - 2) / (8 * nu)) * (q : ℝ) ∧
      eta = ((nu - 2) / (8 * nu)) * (q : ℝ) ∧
      0 < theta ∧ theta < 1 ∧
      0 < A ∧ A < 1 ∧ 0 < eta ∧ eta < 1 ∧
      A ^ 2 < (theta : ℝ) ∧
      0 < nu * (A * (1 - eta) - (theta : ℝ)) -
        (1 - (theta : ℝ)) := by sorry
