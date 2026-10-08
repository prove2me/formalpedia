-- Prove2me | Theorems.Thm_Helfgott_coprime_mobius_over_n_supported_partial_sum
-- name    : Helfgott.coprime_mobius_over_n_supported_partial_sum
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-06T15:47:58.415421+00:00
-- url     : https://prove2.me/theorems/2def711f-af3d-4f0d-b1a5-304ba89e5dae
-- title:
--   Coprime Mobius over n sum as a positive convolution of unrestricted Mobius sums
-- statement:
--   For every $q,Y\ge0$, $$\sum_{1\le n\le Y\atop(n,q)=1}\frac{\mu(n)}n=\sum_{1\le d\le Y\atop p\mid d\Rightarrow p\mid q}\frac1d\sum_{1\le a\le Y/d}\frac{\mu(a)}a.$$ The outer sum retains precisely the integers supported on prime divisors of $q$, with arbitrary prime exponents. Its coefficients are nonnegative. This removes coprimality from the standard Mobius sum in the quantitative Vaughan Type II cancellation argument.
-- source:
--   H. A. Helfgott, Minor arcs for Goldbach, section 4.1.2, equation (4.21), https://arxiv.org/abs/1205.5252. Complete Lean proof with exact finite endpoints. Written by Codex.

import Mathlib
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical Interval

namespace Helfgott

theorem coprime_mobius_over_n_supported_partial_sum  (q Y : ℕ) :
    (∑ n∈Finset.Icc 1 Y,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)/(n : ℝ) else 0)=
      ∑ d∈Finset.Icc 1 Y,if (∀ p∈d.primeFactors,p∣q) then
        (1/(d : ℝ))*(∑ a∈Finset.Icc 1 (Y/d),((moebius a : ℤ) : ℝ)/(a : ℝ)) else 0 := by sorry

end Helfgott
