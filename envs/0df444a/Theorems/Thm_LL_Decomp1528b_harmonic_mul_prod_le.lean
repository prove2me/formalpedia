-- Prove2me | Theorems.Thm_LL_Decomp1528b_harmonic_mul_prod_le
-- name    : LL_Decomp1528b.harmonic_mul_prod_le
-- status  : Open
-- author  : @sthubbar
-- created : 2026-10-30T14:08:57.399983+00:00
-- url     : https://prove2.me/theorems/14008b2f-820a-4dd1-8037-a67c5a3a5d7f
-- title:
--   Harmonic sum times Euler product is at most one
-- statement:
--   For every natural number $N$, $H_N\cdot\prod_{p\le N}(1-1/p)\le 1$, where $H_N=\sum_{n\le N}1/n$ is Mathlib's `harmonic N` cast to $\mathbb R$ and the product runs over primes $p\le N$.
-- source:
--   Hardy and Wright, An Introduction to the Theory of Numbers, Thm 427 proof; Rosser and Schoenfeld, Illinois J. Math. 6 (1962), p. 70 style

import Mathlib

open Real Finset Filter Topology

namespace LL_Decomp1528b
theorem harmonic_mul_prod_le (N : ℕ) :
    (harmonic N : ℝ) * ∏ p ∈ Nat.primesLE N, (1 - (1 : ℝ) / p) ≤ 1 := by sorry
end LL_Decomp1528b
