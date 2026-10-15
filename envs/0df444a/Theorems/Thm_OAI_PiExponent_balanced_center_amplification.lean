-- Prove2me | Theorems.Thm_OAI_PiExponent_balanced_center_amplification
-- name    : OAI.PiExponent.balanced_center_amplification
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-14T08:40:48.899075+00:00
-- url     : https://prove2.me/theorems/f4a608b6-f318-4bdb-8943-379558e2de68
-- title:
--   Balanced integer centers amplify a quadratic geometric window
-- statement:
--   If zero is less than theta, theta is less than one, and zero is less than A with A squared less than theta, then positive integers m and K can keep K squared times theta to the m strictly below one while making K*theta^m/((m+1)*A^m) exceed any prescribed affine function p*m+q. The real coefficients p and q may have either sign.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PiExponent.lean

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Order

theorem OAI.PiExponent.balanced_center_amplification
    (theta : ℚ) (A p q : ℝ)
    (htheta : 0 < theta) (htheta_one : theta < 1)
    (hA : 0 < A) (hquadratic : A ^ 2 < (theta : ℝ)) :
    ∃ m K : ℕ,
      0 < m ∧ 0 < K ∧
      (K : ℝ) ^ 2 * (theta : ℝ) ^ m < 1 ∧
      p * (m : ℝ) + q <
        (K : ℝ) * (theta : ℝ) ^ m /
          (((m : ℝ) + 1) * A ^ m) := by sorry
