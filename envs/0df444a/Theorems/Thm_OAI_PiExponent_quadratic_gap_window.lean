-- Prove2me | Theorems.Thm_OAI_PiExponent_quadratic_gap_window
-- name    : OAI.PiExponent.quadratic_gap_window
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-14T08:40:41.387909+00:00
-- url     : https://prove2.me/theorems/8f53717a-aa05-4597-b076-12d426ee28b8
-- title:
--   A rational quadratic window with positive determinant slack
-- statement:
--   For every real nu greater than two, there are a rational theta strictly between zero and one and real A, eta strictly between zero and one, such that A squared is strictly smaller than theta and the determinant slack nu*(A*(1-eta)-theta)-(1-theta) is positive.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PiExponent.lean

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Order

theorem OAI.PiExponent.quadratic_gap_window (nu : ℝ) (hnu : 2 < nu) :
    ∃ (theta : ℚ) (A eta : ℝ),
      0 < theta ∧ theta < 1 ∧
      0 < A ∧ A < 1 ∧ 0 < eta ∧ eta < 1 ∧
      A ^ 2 < (theta : ℝ) ∧
      0 < nu * (A * (1 - eta) - (theta : ℝ)) -
        (1 - (theta : ℝ)) := by sorry
