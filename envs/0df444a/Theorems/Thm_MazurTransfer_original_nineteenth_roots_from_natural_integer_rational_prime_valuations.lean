-- Prove2me | Theorems.Thm_MazurTransfer_original_nineteenth_roots_from_natural_integer_rational_prime_valuations
-- name    : MazurTransfer.original_nineteenth_roots_from_natural_integer_rational_prime_valuations
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-20T20:10:46.47404+00:00
-- url     : https://prove2.me/theorems/9731b43f-8334-4bce-b483-ad3c75b15d97
-- statement:
--   If all prime valuations of a nonzero natural number are divisible by nineteen, its prime factorization constructs a nineteenth root. The original numerator-denominator criterion and odd exponent handle integers, nonzero rational numbers and rational units, preserving every original nonzero and sign condition. All five complete original propositions are retained. Named downstream consumer: rational nineteenth-power valuation coordinates and the selected pi Selmer radicand bound.

import Mathlib
noncomputable section
open scoped BigOperators

theorem MazurTransfer.original_nineteenth_roots_from_natural_integer_rational_prime_valuations : (∀ (n : ℕ) (hn : n ≠ 0)
    (hval : ∀ p : ℕ, p.Prime → 19 ∣ padicValNat p n), ∃ r : ℕ, r ^ 19 = n) ∧ (∀ (a : ℚ)
    (hval : ∀ p : ℕ, p.Prime → (19 : ℤ) ∣ padicValRat p a)
    (p : ℕ) (hp : p.Prime), 19 ∣ padicValNat p a.num.natAbs ∧ 19 ∣ padicValNat p a.den) ∧ (∀ (n : ℤ) (hn : n ≠ 0)
    (hval : ∀ p : ℕ, p.Prime → 19 ∣ padicValNat p n.natAbs), ∃ r : ℤ, r ^ 19 = n) ∧ (∀ (a : ℚ) (ha : a ≠ 0)
    (hval : ∀ p : ℕ, p.Prime → (19 : ℤ) ∣ padicValRat p a), ∃ b : ℚ, b ^ 19 = a) ∧ (∀ (a : ℚˣ)
    (hval : ∀ p : ℕ, p.Prime → (19 : ℤ) ∣ padicValRat p (a : ℚ)), ∃ b : ℚˣ, b ^ 19 = a) := by sorry
