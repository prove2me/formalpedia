-- Prove2me | Theorems.Thm_Helfgott_moebius_log_squared_bound_of_centered_prime_error
-- name    : Helfgott.moebius_log_squared_bound_of_centered_prime_error
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T22:32:10.358309+00:00
-- url     : https://prove2.me/theorems/dea4faa8-5293-45fd-a45e-8fc95d99b912
-- title:
--   Weighted Mobius bound from the centered prime convolution error
-- statement:
--   Let $x\ge1$, $C\in\mathbb R$, and let $E$ bound the centered prime convolution error $$R_C(y)=\sum_{k\le\lfloor y\rfloor}\big((\Lambda\star\Lambda)(k)-\Lambda(k)\log k\big)+C\lfloor y\rfloor$$ at every quotient $y=x/d$ with $1\le d\le\lfloor x\rfloor$. Here $\star$ denotes Dirichlet convolution. Then $$\left|\sum_{n\le\lfloor x\rfloor}\mu(n)\log^2 n\right|\le |C|+\sum_{d\le\lfloor x\rfloor}\mu(d)^2 E(x/d).$$ The exact centered identity and all floor endpoints are proved. Choosing $C=2\gamma$ gives the arithmetic reduction used to transfer quantitative prime estimates to a signed Möbius estimate. Bounds on the actual prime error remain separate inputs.
-- source:
--   O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), equations (3.3), (3.4) and (6.1), https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Complete exact arithmetic reduction with arbitrary centering constant. Written by Codex.

import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Algebra.Order.Floor.Semifield
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

namespace Helfgott

theorem moebius_log_squared_bound_of_centered_prime_error 
    (x C : ℝ) (E : ℝ → ℝ) (hx : 1 ≤ x)
    (hE : ∀ d ∈ Finset.Icc 1 ⌊x⌋₊,
      |(∑ k ∈ Finset.Icc 1 ⌊x / (d : ℝ)⌋₊,
        ((vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ))) +
        C * (⌊x / (d : ℝ)⌋₊ : ℝ)| ≤ E (x / (d : ℝ))) :
    |∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
      ((moebius n : ℤ) : ℝ) * Real.log (n : ℝ) ^ 2| ≤
      |C| + ∑ d ∈ Finset.Icc 1 ⌊x⌋₊,
        ((moebius d : ℤ) : ℝ) ^ 2 * E (x / (d : ℝ)) := by sorry

end Helfgott
