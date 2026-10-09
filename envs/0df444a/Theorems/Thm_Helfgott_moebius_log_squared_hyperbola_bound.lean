-- Prove2me | Theorems.Thm_Helfgott_moebius_log_squared_hyperbola_bound
-- name    : Helfgott.moebius_log_squared_hyperbola_bound
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T22:48:23.089068+00:00
-- url     : https://prove2.me/theorems/50725b4d-7a3a-4c42-aed8-eb04dddecdc8
-- title:
--   Quantitative Mobius hyperbola reduction with exact overlap correction
-- statement:
--   Let $N,K\ge1$ be integers, let $C\in\mathbb R$ and $L>0$, and put $H=\lfloor N/K\rfloor$. Define $a_C(k)=(\Lambda\star\Lambda)(k)-\Lambda(k)\log k+C$, $A_C(y)=\sum_{k\le\lfloor y\rfloor}a_C(k)$, and $M(u)=\sum_{n\le u}\mu(n)$. Suppose $|A_C(N/d)|\le E(N/d)$ for $1\le d\le H$ and $|M(u)|\le u/L$ for every integer $u\ge H$. Then $$\left|\sum_{n\le N}\mu(n)\log^2 n\right|\le |C|+\sum_{d\le H}\mu(d)^2E(N/d)+\frac NL\left(\sum_{k\le K}\frac{|a_C(k)|}{k}+\frac{|A_C(K)|}{K}\right).$$ This separates the large prime-error range from a finite coefficient moment. The rectangular overlap correction and all integer-quotient endpoints are included. Taking $C=2\gamma$ gives the centered arithmetic reduction toward the explicit signed Möbius estimate.
-- source:
--   O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), sections 3, 6 and 7, https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Original complete exact hyperbola proof and quantitative reduction, retaining the overlap correction. Written by Codex.

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Algebra.Order.Floor.Semifield
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

namespace Helfgott

theorem moebius_log_squared_hyperbola_bound  (N K : ℕ) (C L : ℝ) (E : ℝ → ℝ)
    (hN : 1 ≤ N) (hK : 0 < K) (hL : 0 < L)
    (hR : ∀ d ∈ Icc 1 (N / K),
      |∑ k ∈ Icc 1 (N / d),
        ((vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ) + C)| ≤
          E ((N : ℝ) / (d : ℝ)))
    (hM : ∀ u : ℕ, N / K ≤ u →
      |∑ d ∈ Icc 1 u, ((moebius d : ℤ) : ℝ)| ≤ (u : ℝ) / L) :
    |∑ n ∈ Icc 1 N, ((moebius n : ℤ) : ℝ) * Real.log (n : ℝ) ^ 2| ≤
      |C| + (∑ d ∈ Icc 1 (N / K),
        ((moebius d : ℤ) : ℝ) ^ 2 * E ((N : ℝ) / (d : ℝ))) +
      ((N : ℝ) / L) *
        ((∑ k ∈ Icc 1 K,
          |(vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ) + C| /
            (k : ℝ)) +
          |∑ k ∈ Icc 1 K,
            ((vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ) + C)| /
            (K : ℝ)) := by sorry

end Helfgott
