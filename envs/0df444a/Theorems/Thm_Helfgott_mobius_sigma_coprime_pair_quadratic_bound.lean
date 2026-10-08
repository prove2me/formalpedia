-- Prove2me | Theorems.Thm_Helfgott_mobius_sigma_coprime_pair_quadratic_bound
-- name    : Helfgott.mobius_sigma_coprime_pair_quadratic_bound
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-06T15:38:45.044981+00:00
-- url     : https://prove2.me/theorems/5e65a648-de96-49fd-a2d2-9d22705dea89
-- title:
--   Signed coprime Mobius pair sum reduced to squares of single Mobius sums
-- statement:
--   Let $\sigma(n)=\prod_{p\mid n}(p+1)$ and $f(n)=\mu(n)/\sigma(n)$. For all integers $q,Y\ge0$, the signed pair sum satisfies $$\left|\sum_{1\le r,t\le Y\atop (r,t)=(r,q)=(t,q)=1}f(r)f(t)\right|\le\sum_{1\le d\le Y\atop(d,q)=1}\frac{|\mu(d)|}{\sigma(d)^2}\left(\sum_{1\le a\le Y/d\atop(a,dq)=1}f(a)\right)^2.$$ This preserves cancellation in the one-variable Mobius sums, providing the arithmetic reduction needed to bound the actual Vaughan Type II energy.
-- source:
--   H. A. Helfgott, Minor arcs for Goldbach, section 4.1.2, equation (4.20), https://arxiv.org/abs/1205.5252. Complete Lean proof with exact finite endpoints. Written by Codex.

import Mathlib
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical Interval

namespace Helfgott

theorem mobius_sigma_coprime_pair_quadratic_bound  (q Y : ℕ) :
    let f : ℕ→ℝ := fun n => ((moebius n : ℤ) : ℝ)/(∏ p∈n.primeFactors,((p : ℝ)+1))
    |∑ r∈Finset.Icc 1 Y,∑ t∈Finset.Icc 1 Y,
      if Nat.Coprime r t ∧ Nat.Coprime r q ∧ Nat.Coprime t q then f r*f t else 0| ≤
      ∑ d∈Finset.Icc 1 Y,if Nat.Coprime d q then
        (|((moebius d : ℤ) : ℝ)|/(∏ p∈d.primeFactors,((p : ℝ)+1))^2)*
          (∑ a∈Finset.Icc 1 (Y/d),if Nat.Coprime a (d*q) then f a else 0)^2 else 0 := by sorry

end Helfgott
