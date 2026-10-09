-- Prove2me | Theorems.Thm_Helfgott_moebius_log_squared_bound_of_prime_error_and_finite_moment
-- name    : Helfgott.moebius_log_squared_bound_of_prime_error_and_finite_moment
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T00:05:14.114346+00:00
-- url     : https://prove2.me/theorems/73ec7acb-9663-4562-b524-b2c3155fb5d6
-- title:
--   Explicit harmonic-density Mobius hyperbola bound
-- statement:
--   Let $N,K$ be positive integers, $H=\lfloor N/K\rfloor\ge10000$, and let $L>0$, $\varepsilon\ge0$, $B,C\in\mathbb R$. Put $a_C(k)=(\Lambda*\Lambda)(k)-\Lambda(k)\log k+C$ and $A_C(u)=\sum_{k\le u}a_C(k)$. Suppose $|A_C(\lfloor N/d\rfloor)|\le\varepsilon N/d$ for every integer $1\le d\le H$, $|M(u)|\le u/L$ for every integer $u\ge H$, and
--   $$\sum_{k\le K}|a_C(k)|/k+|A_C(K)|/K\le LB.$$
--   Then
--   $$\left|\sum_{n\le N}\mu(n)\log^2n\right|\le |C|+N\left[\varepsilon\left(\frac6{\pi^2}\log(N/K)+1.166\right)+B\right].$$
--   The squarefree harmonic factor is unconditional, including its finite numerical baseline. The prime-error envelope, coarse summatory estimate, and finite convolution moment remain explicit hypotheses for the subsequent minor-arc assembly.
-- source:
--   O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 7, https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Correct hyperbola overlap is retained; the full squarefree harmonic estimate is reused from an accepted independent proof. Written by Codex.

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Algebra.Order.Floor.Semifield
import Theorems.Thm_Helfgott_squarefree_harmonic_log_upper_bound
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

namespace Helfgott

theorem moebius_log_squared_bound_of_prime_error_and_finite_moment 
    (N K : ℕ) (C L ε B : ℝ) (hK : 0 < K) (hH : 10000 ≤ N / K)
    (hL : 0 < L) (hε : 0 ≤ ε)
    (hR : ∀ d ∈ Icc 1 (N / K),
      |∑ k ∈ Icc 1 (N / d),
        ((vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ) + C)| ≤
          ε * ((N : ℝ) / (d : ℝ)))
    (hM : ∀ u : ℕ, N / K ≤ u →
      |∑ d ∈ Icc 1 u, ((moebius d : ℤ) : ℝ)| ≤ (u : ℝ) / L)
    (hfinite :
      ((∑ k ∈ Icc 1 K,
        |(vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ) + C| /
          (k : ℝ)) +
        |∑ k ∈ Icc 1 K,
          ((vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ) + C)| /
          (K : ℝ)) ≤ L * B) :
    |∑ n ∈ Icc 1 N, ((moebius n : ℤ) : ℝ) * Real.log (n : ℝ) ^ 2| ≤
      |C| + (N : ℝ) *
        (ε * ((6 / Real.pi ^ 2) * Real.log ((N : ℝ) / (K : ℝ)) + 583 / 500) + B) := by sorry

end Helfgott
