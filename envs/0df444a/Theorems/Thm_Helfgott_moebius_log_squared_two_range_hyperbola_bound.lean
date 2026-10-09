-- Prove2me | Theorems.Thm_Helfgott_moebius_log_squared_two_range_hyperbola_bound
-- name    : Helfgott.moebius_log_squared_two_range_hyperbola_bound
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T00:16:25.199984+00:00
-- url     : https://prove2.me/theorems/78075ce3-5b71-4f99-b55f-3904008ccc4d
-- title:
--   Mobius hyperbola bound with two prime-error envelopes
-- statement:
--   Let $N,K_0,K_1$ be positive integers with $K_0\le K_1$, and put $H_i=\lfloor N/K_i\rfloor$, with $H_1\ge10000$. Let $\rho=6/\pi^2$, $L>0$, $\varepsilon_0,\varepsilon_1\ge0$, and $B,C\in\mathbb R$. Write $a_C(k)=(\Lambda*\Lambda)(k)-\Lambda(k)\log k+C$, $A_C(u)=\sum_{k\le u}a_C(k)$, and $M(u)=\sum_{n\le u}\mu(n)$. Suppose $|A_C(\lfloor N/d\rfloor)|\le\varepsilon_1N/d$ for $1\le d\le H_1$, and $|A_C(\lfloor N/d\rfloor)|\le\varepsilon_0N/d$ for $H_1<d\le H_0$. Suppose also that $|M(u)|\le u/L$ for every integer $u\ge H_0$ and
--   $$\sum_{k\le K_0}|a_C(k)|/k+|A_C(K_0)|/K_0\le LB.$$
--   Then
--   $$\left|\sum_{n\le N}\mu(n)\log^2n\right|\le |C|+N\left[\varepsilon_1\big(\rho\log(N/K_1)+1.166\big)+\varepsilon_0\left(\rho\log(H_0/H_1)+9/\sqrt{H_1}+\rho/H_1\right)+B\right].$$
--   Both harmonic estimates are proved unconditionally. The distinct envelopes retain the stronger prime-error estimate for the larger quotients, with the middle interval and exact floor effects explicit.
-- source:
--   Independent two-range refinement of the exact Mobius hyperbola argument in O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Written by Codex.

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Algebra.Order.Floor.Semifield
import Theorems.Thm_Helfgott_squarefree_harmonic_log_upper_bound
import Theorems.Thm_Helfgott_squarefree_harmonic_interval_log_bound
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

namespace Helfgott

theorem moebius_log_squared_two_range_hyperbola_bound 
    (N K0 K1 : ℕ) (C L ε0 ε1 B : ℝ)
    (hK0 : 0 < K0) (hK01 : K0 ≤ K1) (hH1 : 10000 ≤ N / K1)
    (hL : 0 < L) (hε0 : 0 ≤ ε0) (hε1 : 0 ≤ ε1)
    (hRhigh : ∀ d ∈ Icc 1 (N / K1),
      |∑ k ∈ Icc 1 (N / d),
        ((vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ) + C)| ≤
          ε1 * ((N : ℝ) / (d : ℝ)))
    (hRmiddle : ∀ d ∈ Ioc (N / K1) (N / K0),
      |∑ k ∈ Icc 1 (N / d),
        ((vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ) + C)| ≤
          ε0 * ((N : ℝ) / (d : ℝ)))
    (hM : ∀ u : ℕ, N / K0 ≤ u →
      |∑ d ∈ Icc 1 u, ((moebius d : ℤ) : ℝ)| ≤ (u : ℝ) / L)
    (hfinite :
      ((∑ k ∈ Icc 1 K0,
        |(vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ) + C| /
          (k : ℝ)) +
        |∑ k ∈ Icc 1 K0,
          ((vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ) + C)| /
          (K0 : ℝ)) ≤ L * B) :
    |∑ n ∈ Icc 1 N, ((moebius n : ℤ) : ℝ) * Real.log (n : ℝ) ^ 2| ≤
      |C| + (N : ℝ) *
        (ε1 * ((6 / Real.pi ^ 2) * Real.log ((N : ℝ) / (K1 : ℝ)) + 583 / 500) +
         ε0 * ((6 / Real.pi ^ 2) * Real.log (((N / K0 : ℕ) : ℝ) / ((N / K1 : ℕ) : ℝ)) +
           9 / Real.sqrt ((N / K1 : ℕ) : ℝ) + (6 / Real.pi ^ 2) / ((N / K1 : ℕ) : ℝ)) + B) := by sorry

end Helfgott
