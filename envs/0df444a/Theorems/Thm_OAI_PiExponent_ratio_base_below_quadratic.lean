-- Prove2me | Theorems.Thm_OAI_PiExponent_ratio_base_below_quadratic
-- name    : OAI.PiExponent.ratio_base_below_quadratic
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-14T09:05:52.224995+00:00
-- url     : https://prove2.me/theorems/07ef9cc7-408d-4dbe-987f-d726a248c2ac
-- title:
--   Choose a growth base below the quadratic ratio
-- statement:
--   From positive theta and A with A squared strictly below theta, choose a real base greater than one whose square is still below theta divided by A squared.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PiExponent.lean

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Order

theorem OAI.PiExponent.ratio_base_below_quadratic
    (theta : ℚ) (A : ℝ)
    (htheta : 0 < theta) (hA : 0 < A)
    (hquadratic : A ^ 2 < (theta : ℝ)) :
    ∃ R : ℝ, 1 < R ∧ R ^ 2 < (theta : ℝ) / A ^ 2 := by sorry
