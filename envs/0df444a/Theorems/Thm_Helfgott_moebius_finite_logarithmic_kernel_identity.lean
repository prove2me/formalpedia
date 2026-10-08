-- Prove2me | Theorems.Thm_Helfgott_moebius_finite_logarithmic_kernel_identity
-- name    : Helfgott.moebius_finite_logarithmic_kernel_identity
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-06T16:53:14.449991+00:00
-- url     : https://prove2.me/theorems/51b759fc-3a03-4777-a5d0-bdad78757c55
-- title:
--   Exact finite logarithmic Mobius cancellation kernel
-- statement:
--   For every integer $N\ge1$, $$\sum_{d\le N}\mu(d)\sum_{k\le N/d}\log\frac{N}{dk}=\log N.$$ Every inner endpoint is the actual integer quotient. This exact arithmetic logarithmic kernel is the finite cancellation behind El Marraki\'s improved conversion from summatory Mobius bounds to reciprocal Mobius-sum bounds.
-- source:
--   O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, identity (9.2), https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Complete finite arithmetic kernel proof toward the quantitative Mobius estimate needed in Helfgott section 4.1. Written by Codex.

import Mathlib
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical Interval

namespace Helfgott

theorem moebius_finite_logarithmic_kernel_identity  (N : ℕ) (hN : 1 ≤ N) :
    (∑ d∈Finset.Icc 1 N,∑ k∈Finset.Icc 1 (N/d),
      ((moebius d : ℤ) : ℝ)*Real.log ((N : ℝ)/((d*k : ℕ) : ℝ))) = Real.log (N : ℝ) := by sorry

end Helfgott
