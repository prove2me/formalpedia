-- Prove2me | Theorems.Thm_OddGoldbach19_interval_reciprocal_weighted_sifted_five
-- name    : OddGoldbach19.interval_reciprocal_weighted_sifted_five
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-30T17:05:50.807269+00:00
-- url     : https://prove2.me/theorems/db7c218a-bab0-4951-8a99-df9b0e44250d
-- title:
--   Coefficient-five reciprocal sieve on arbitrary natural intervals
-- statement:
--   The reciprocal weighted pair-sieve bound with denominator N+5*q*z holds for any finite set A contained in [M,M+N). Squarefree moduli q<=z contain1, z>=1, d is even, and no prime factor of any modulus divides n(n+d) for n in A.
-- source:
--   Interval translation adapted from public Apache2.0 Prove2Me accepted proof ef73b684-e41f-4ba6-be36-cd6b0bd75f07. Uses the new proved coefficient-five nonuniform large sieve and the existing primitive Fourier energy inequality.

import Mathlib
import Definitions.Def_TaoFivePrimes_SingularSeries
open scoped BigOperators

theorem OddGoldbach19.interval_reciprocal_weighted_sifted_five
    (Q : Finset ℕ+) (h1 : 1 ∈ Q) (M N d : ℕ) (z : ℝ) (hz : 1 ≤ z)
    (hQ : ∀ q ∈ Q, Squarefree (q : ℕ) ∧ ((q : ℕ) : ℝ) ≤ z)
    (hd : 2 ∣ d) (A : Finset ℕ) (hAN : A ⊆ Finset.Ico M (M + N))
    (hA : ∀ q ∈ Q, ∀ n ∈ A, ∀ p ∈ (q : ℕ).primeFactors, ¬ p ∣ n*(n+d)) :
    (A.card : ℝ) ≤ (∑ q ∈ Q,
      (∏ p ∈ (q : ℕ).primeFactors,
        if p ∣ d then 1 / ((p : ℝ)-1) else 2 / ((p : ℝ)-2)) /
      ((N : ℝ)+5*((q : ℕ) : ℝ)*z))⁻¹ := by sorry
