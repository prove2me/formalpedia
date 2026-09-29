-- Prove2me | Theorems.Thm_Int_exists_not_dvd_and_le_and_not_isSquare_and_forall_prime_of_sq_sub_four_mul_ne_zero
-- name    : Int.exists_not_dvd_and_le_and_not_isSquare_and_forall_prime_of_sq_sub_four_mul_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/167fb6e0-42f9-5284-a50f-f997b882bcb6
-- title:
--   Normalising a quadratic translate: non-square, primitive, prime to p
-- statement:
--   Let $t,q$ be integers with $t^2-4q\neq 0$, let $p$ be a prime number, and write $g(a)=a^2+ta+q$ for $a\in\mathbb Z$. Assume there exists at least one integer $a_0$ with $p\nmid g(a_0)$. Then there exists an integer $a$ such that all four of the following hold: $p\nmid g(a)$; $g(a)\ge 2$; $g(a)$ is not a square in $\mathbb Z$ (i.e. there is no integer $r$ with $g(a)=r\cdot r$); and for every prime number $\ell$, if $\ell$ divides $2a+t$ then $\ell^2$ does not divide $g(a)$. (Note that the last three conjuncts are, in the Lean statement, grouped under the second component of the conjunction, the first conjunct being the non-divisibility by $p$.) If $\alpha$ is a root of $X^2-tX+q$, then $2a+t$ and $g(a)$ are the trace and norm of $\alpha+a$, so the conclusion produces a translate $\alpha+a$ of norm prime to $p$, of norm at least $2$ and not a perfect square, and divisible by no rational prime.
--
--   This is the opening normalisation step in Deuring's proof of his lifting theorem for endomorphisms of elliptic curves in characteristic $p$, in the form used by Lang: an endomorphism with characteristic polynomial $X^2-tX+q$ is replaced by a translate $\alpha+a$ whose degree is prime to $p$, is not a square and is not divisible by the square of any prime dividing the trace. It is used here in the construction of a variable change compatible with reduction for a Weierstrass curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Int_exists_not_dvd_and_le_and_not_isSquare_and_forall_prime_of_sq_sub_four_mul_ne_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Int.exists_not_dvd_and_le_and_not_isSquare_and_forall_prime_of_sq_sub_four_mul_ne_zero (t q : ℤ) (hD : t ^ 2 - 4 * q ≠ 0) (p : ℕ) [Fact p.Prime] (h : ∃ a₀ : ℤ, ¬ (p : ℤ) ∣ a₀ ^ 2 + t * a₀ + q) : ∃ a : ℤ, ¬ (p : ℤ) ∣ a ^ 2 + t * a + q ∧ 2 ≤ a ^ 2 + t * a + q ∧ ¬ IsSquare (a ^ 2 + t * a + q) ∧ ∀ ℓ : ℕ, ℓ.Prime → (ℓ : ℤ) ∣ 2 * a + t → ¬ (ℓ : ℤ) ^ 2 ∣ a ^ 2 + t * a + q := by sorry
