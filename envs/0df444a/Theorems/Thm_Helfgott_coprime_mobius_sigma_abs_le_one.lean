-- Prove2me | Theorems.Thm_Helfgott_coprime_mobius_sigma_abs_le_one
-- name    : Helfgott.coprime_mobius_sigma_abs_le_one
-- status  : Proved
-- author  : @flyingviper
-- created : 2026-11-11T21:41:36.677614+00:00
-- url     : https://prove2.me/theorems/4a94bc38-a47e-48fe-b2af-b4dd627ca982
-- title:
--   Uniform unit bound for coprime Mobius sums with sigma denominators
-- statement:
--   For all natural numbers $q,N$, put $P(n)=\prod_{p\mid n}(p+1)$. Then
--   $$\left|\sum_{\substack{1\le n\le N\\(n,q)=1}}\frac{\mu(n)}{P(n)}\right|\le1.$$
--   On squarefree integers, $P(n)$ is the sum-of-divisors function $\sigma(n)$. This unconditional unit bound improves constants in the complementary-divisor energy estimates used for Type II sums.
-- source:
--   Finite convex averaging of coprime Mobius reciprocal sums, formalized for the Prove2Me Weak Goldbach mission.

import Mathlib
open Finset ArithmeticFunction
open scoped BigOperators

theorem Helfgott.coprime_mobius_sigma_abs_le_one (q N : ℕ) :
    |∑ n ∈ Icc 1 N, if Nat.Coprime n q then
      ((moebius n:ℤ):ℝ)/(∏ p ∈ n.primeFactors, ((p:ℝ)+1)) else 0|≤1 := by sorry
