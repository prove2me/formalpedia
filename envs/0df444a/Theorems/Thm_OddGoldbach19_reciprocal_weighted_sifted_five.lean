-- Prove2me | Theorems.Thm_OddGoldbach19_reciprocal_weighted_sifted_five
-- name    : OddGoldbach19.reciprocal_weighted_sifted_five
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-30T16:42:49.136775+00:00
-- url     : https://prove2.me/theorems/b7682373-d9c1-4ea9-8d27-4b22e993a46e
-- title:
--   Reciprocal weighted pair sieve with coefficient five
-- statement:
--   Let Q be a finite set of positive squarefree integers containing1, each at most a real z>=1. Let d be an even natural number and A a finite subset of0,...,N-1. Suppose every integer in A avoids each prime factor of every q in Q as a divisor of n(n+d). Then |A| is bounded by the reciprocal of the sum over q in Q of the product of local pair-sieve weights divided by N+5qz. A prime factor p contributes1/(p-1) if p divides d, and2/(p-2) otherwise. This is the same pair-sieve model as the existing coefficient16 theorem, with a smaller verified denominator coefficient.
-- source:
--   Derived refinement of existing public Prove2Me weighted Hilbert and pair-sieve proof chain; see proof explanation for precise reused accepted submission IDs.

import Mathlib
open scoped BigOperators ComplexConjugate

theorem OddGoldbach19.reciprocal_weighted_sifted_five
    (Q : Finset ℕ+) (h1 : 1 ∈ Q) (N d : ℕ) (z : ℝ) (hz : 1 ≤ z)
    (hQ : ∀ q ∈ Q, Squarefree (q : ℕ) ∧ ((q : ℕ) : ℝ) ≤ z)
    (hd : 2 ∣ d) (A : Finset ℕ) (hAN : A ⊆ Finset.range N)
    (hA : ∀ q ∈ Q, ∀ n ∈ A, ∀ p ∈ (q : ℕ).primeFactors, ¬ p ∣ n*(n+d)) :
    (A.card : ℝ) ≤ (∑ q ∈ Q,
      (∏ p ∈ (q : ℕ).primeFactors,
        if p ∣ d then 1 / ((p : ℝ)-1) else 2 / ((p : ℝ)-2)) /
      ((N : ℝ)+5*((q : ℕ) : ℝ)*z))⁻¹ := by sorry
