-- Prove2me | Theorems.Thm_MasulloRH_smooth_bilateral_prime_test_preparation
-- name    : MasulloRH.smooth_bilateral_prime_test_preparation
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T10:40:27.80646+00:00
-- url     : https://prove2.me/theorems/93b783e8-bfb4-40ca-83a9-775161fcab8f
-- title:
--   A single smooth compact test preparation preserves both arithmetic tails and kills the left-edge moment
-- statement:
--   There are fixed smooth real multipliers a and c, with c compactly supported, such that the explicit linear transform g=a f−c ∫a f exp(−x/2) takes every smooth compact real log test to a smooth compact test, vanishes on |x|≤1/8, agrees with f for x≥1/2 and with exp(x)f for x≤−1/2, and has zero left-edge moment. These fixed thresholds lie in the gap to the first prime log norms.
-- source:
--   Masullo closed global Euler layers and frozen finite-place distribution (12.4.1.3); bilateral log-test preparation in the rational trivial character sector.

import Mathlib
open MeasureTheory

theorem MasulloRH.smooth_bilateral_prime_test_preparation :
    ∃ (a c : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) a ∧
      ContDiff ℝ (⊤ : ℕ∞) c ∧ HasCompactSupport c ∧
      ∀ f : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
        let J := ∫ x : ℝ, a x * f x * Real.exp (-x/2)
        let g := fun x : ℝ => a x * f x - J * c x
        ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧
        (∀ x : ℝ, |x| ≤ 1/8 → g x = 0) ∧
        (∀ x : ℝ, 1/2 ≤ x → g x = f x) ∧
        (∀ x : ℝ, x ≤ -(1/2) → g x = Real.exp x * f x) ∧
        (∫ x : ℝ, g x * Real.exp (-x/2)) = 0 := by sorry
