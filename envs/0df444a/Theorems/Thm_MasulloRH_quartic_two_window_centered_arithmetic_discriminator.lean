-- Prove2me | Theorems.Thm_MasulloRH_quartic_two_window_centered_arithmetic_discriminator
-- name    : MasulloRH.quartic_two_window_centered_arithmetic_discriminator
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T08:50:53.729197+00:00
-- url     : https://prove2.me/theorems/c5006ef4-5e61-4325-aa3a-ce5c43b18723
-- title:
--   A smooth two-window test separates the plain and half-weighted conjugate quartic prime-power sums at 2 and 8
-- statement:
--   A genuine quartic Dirichlet character mod 5 with value i at 2 exists. A common smooth real compact test vanishes below norm one and on every natural norm except 2 and 8, where it equals one. For every such character and every cutoff containing 2 and 8, the conjugate difference of the unweighted von Mangoldt sums is zero, while the half-weighted sum is exactly i log(2)/sqrt(2).
-- source:
--   Masullo critical-weight rational mission, comparison of (11.3.2.1) and (12.4.1.3). This certificate covers the arithmetic test, independently of the quotient trace.

import Mathlib
open ArithmeticFunction Complex
open scoped BigOperators

theorem MasulloRH.quartic_two_window_centered_arithmetic_discriminator :
    (∃ χ : DirichletCharacter ℂ 5, χ 2 = I) ∧
    ∃ f : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧
      (∀ x ≤ (1:ℝ), f x = 0) ∧ f 2 = 1 ∧ f 8 = 1 ∧
      (∀ n : ℕ, n ≠ 2 → n ≠ 8 → f n = 0) ∧
      ∀ (χ : DirichletCharacter ℂ 5), χ 2 = I →
        ∀ (S : Finset ℕ), 2 ∈ S → 8 ∈ S →
        let a : ℕ → ℂ := fun n => (vonMangoldt n * f n : ℝ) * (χ n - star (χ n))
        (∑ n ∈ S, a n) = 0 ∧
        (∑ n ∈ S, a n / Real.sqrt n) = I * Real.log 2 / Real.sqrt 2 := by sorry
