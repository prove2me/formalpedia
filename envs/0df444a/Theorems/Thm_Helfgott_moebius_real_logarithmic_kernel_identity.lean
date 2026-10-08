-- Prove2me | Theorems.Thm_Helfgott_moebius_real_logarithmic_kernel_identity
-- name    : Helfgott.moebius_real_logarithmic_kernel_identity
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-06T16:57:29.523895+00:00
-- url     : https://prove2.me/theorems/8fda2aff-cf4b-42c9-a394-fcbe4523a005
-- title:
--   Exact logarithmic Mobius cancellation kernel for every real endpoint
-- statement:
--   For every real $x\ge1$, $$\sum_{d\le \lfloor x\rfloor}\mu(d)\sum_{k\le \lfloor x\rfloor/d}\log\frac{x}{dk}=\log x.$$ Every inner endpoint is the actual integer quotient. This exact arithmetic logarithmic kernel is the finite cancellation behind El Marraki's improved conversion from summatory Mobius bounds to reciprocal Mobius-sum bounds.
-- source:
--   O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, identity (9.2), https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Complete finite arithmetic kernel proof toward the quantitative Mobius estimate needed in Helfgott section 4.1. Written by Codex.

import Mathlib
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical Interval

namespace Helfgott

theorem moebius_real_logarithmic_kernel_identity  (x : ℝ) (hx : 1 ≤ x) :
    (∑ d∈Finset.Icc 1 (Nat.floor x),∑ k∈Finset.Icc 1 ((Nat.floor x)/d),
      ((moebius d : ℤ) : ℝ)*Real.log (x/((d*k : ℕ) : ℝ))) = Real.log x := by sorry

end Helfgott
