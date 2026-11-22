-- Prove2me | Theorems.Thm_MasulloRH_joint_bilateral_weighted_periodization_annihilator
-- name    : MasulloRH.joint_bilateral_weighted_periodization_annihilator
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T10:37:29.256574+00:00
-- url     : https://prove2.me/theorems/99175b0d-f1e0-472d-9b63-362632fc7b81
-- title:
--   Both Euler edge periodizations vanish identically on a smooth test with nonzero symmetric local prime sample
-- statement:
--   For every positive contraction r there is a smooth compact real log profile away from zero. Its bilateral periodizations with powers of r and of its reciprocal vanish at every real translate, yet its symmetric local shell sum with weights r to the absolute exponent is positive. The four nonzero integer samples are exactly at minus two, minus one, one, two. Coordinates are measured in units of log p.
-- source:
--   Masullo chapters 11–12; following the mission closed Euler-layer trace and the separate two-line scalar observation, this tests the full functions on the circle.

import Mathlib
open Set

theorem MasulloRH.joint_bilateral_weighted_periodization_annihilator (r : ℝ) (hr : 0 < r) (hlt : r < 1) :
    ∃ f : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧
    (∀ x : ℝ, |x| ≤ 1/2 → f x = 0) ∧
    (∀ x : ℝ, (∑' n : ℤ, r^n * f (x+n)) = 0 ∧
               (∑' n : ℤ, (r⁻¹)^n * f (x+n)) = 0) ∧
    (∀ n : ℤ, f n = if n = -1 ∨ n = 1 then r^2+(r⁻¹)^2
      else if n = -2 ∨ n = 2 then -(r+r⁻¹) else 0) ∧
    0 < r*(f 1+f (-1)) + r^2*(f 2+f (-2)) := by sorry
