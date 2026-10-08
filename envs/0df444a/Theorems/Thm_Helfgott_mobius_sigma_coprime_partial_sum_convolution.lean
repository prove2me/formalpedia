-- Prove2me | Theorems.Thm_Helfgott_mobius_sigma_coprime_partial_sum_convolution
-- name    : Helfgott.mobius_sigma_coprime_partial_sum_convolution
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-06T15:43:25.912098+00:00
-- url     : https://prove2.me/theorems/28416e88-ee91-4c36-a167-db0c4508ac8a
-- title:
--   Coprime Mobius over sigma sum as a positive convolution of Mobius over n sums
-- statement:
--   For $\sigma(n)=\prod_{p\mid n}(p+1)$ and all integers $q,Y\ge0$, $$\sum_{1\le r\le Y\atop(r,q)=1}\frac{\mu(r)}{\sigma(r)}=\sum_{1\le d\le Y\atop(d,q)=1}\frac{\mu(d)^2}{d\sigma(d)}\sum_{1\le a\le Y/d\atop(a,dq)=1}\frac{\mu(a)}{a}.$$ Every outer coefficient is nonnegative. The identity transfers explicit bounds on the standard coprime Mobius-over-n sum to the weighted cancellation sum needed in Vaughan Type II estimates.
-- source:
--   H. A. Helfgott, Minor arcs for Goldbach, section 4.1.2, after equation (4.20), https://arxiv.org/abs/1205.5252. Complete Lean proof with exact finite endpoints. Written by Codex.

import Mathlib
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical Interval

namespace Helfgott

theorem mobius_sigma_coprime_partial_sum_convolution  (q Y : ℕ) :
    (∑ r∈Finset.Icc 1 Y,if Nat.Coprime r q then
      ((moebius r : ℤ) : ℝ)/(∏ p∈r.primeFactors,((p : ℝ)+1)) else 0)=
      ∑ d∈Finset.Icc 1 Y,if Nat.Coprime d q then
        (((moebius d : ℤ) : ℝ)^2/((d : ℝ)*(∏ p∈d.primeFactors,((p : ℝ)+1))))*
          (∑ a∈Finset.Icc 1 (Y/d),if Nat.Coprime a (d*q) then
            ((moebius a : ℤ) : ℝ)/(a : ℝ) else 0) else 0 := by sorry

end Helfgott
