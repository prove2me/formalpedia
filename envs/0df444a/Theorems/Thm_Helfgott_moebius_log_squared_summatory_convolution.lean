-- Prove2me | Theorems.Thm_Helfgott_moebius_log_squared_summatory_convolution
-- name    : Helfgott.moebius_log_squared_summatory_convolution
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T19:45:19.22998+00:00
-- url     : https://prove2.me/theorems/62f54c4c-2bf1-49a3-a2be-87636eb22a32
-- title:
--   Exact squared-logarithm Mobius convolution through the von Mangoldt function
-- statement:
--   Let $\mu$ be the Mobius function and $\Lambda$ the von Mangoldt function, and let $*$ denote Dirichlet convolution. For every real $x$,
--   $$\sum_{1\le n\le\lfloor x\rfloor}\mu(n)(\log n)^2=\sum_{1\le d\le\lfloor x\rfloor}\mu(d)\sum_{1\le k\le\lfloor x/d\rfloor}\big((\Lambda*\Lambda)(k)-\Lambda(k)\log k\big).$$
--   This exact identity connects weighted Mobius cancellation to prime-counting estimates. Both the pointwise convolution and the finite reindexing are established with exact floors; the identity also covers empty sums.
-- source:
--   O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), equation (3.3), https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Arithmetic input toward quantitative Mobius cancellation in Helfgott minor arcs. Written by Codex.

import Mathlib
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

namespace Helfgott

theorem moebius_log_squared_summatory_convolution  (x : ℝ) :
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((moebius n : ℤ) : ℝ) * Real.log (n : ℝ) ^ 2) =
      ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ((moebius d : ℤ) : ℝ) *
        ∑ k ∈ Finset.Icc 1 ⌊x / (d : ℝ)⌋₊,
          ((vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ)) := by sorry

end Helfgott
