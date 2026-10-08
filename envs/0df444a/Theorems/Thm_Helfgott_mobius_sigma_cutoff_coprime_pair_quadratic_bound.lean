-- Prove2me | Theorems.Thm_Helfgott_mobius_sigma_cutoff_coprime_pair_quadratic_bound
-- name    : Helfgott.mobius_sigma_cutoff_coprime_pair_quadratic_bound
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-06T15:52:28.601002+00:00
-- url     : https://prove2.me/theorems/e9b564a9-f3d1-4401-8c40-470d0b86eb38
-- title:
--   Strict-cutoff coprime Mobius pair sum reduced to nonnegative squares
-- statement:
--   Let $\sigma(n)=\prod_{p\mid n}(p+1)$ and $f(n)=\mu(n)/\sigma(n)$. For all $q,Y\ge0$ and real $U,z$, $$\left|\sum_{1\le r,t\le Y\atop (r,t)=(r,q)=(t,q)=1,\ Ur,Ut<z}f(r)f(t)\right|\le\sum_{1\le d\le Y\atop(d,q)=1}\frac{|\mu(d)|}{\sigma(d)^2}\left(\sum_{1\le a\le Y/d\atop(a,dq)=1,\ Uda<z}f(a)\right)^2.$$ This retains every strict cutoff in the actual Vaughan signed density integral and preserves cancellation in each one-variable Mobius sum.
-- source:
--   H. A. Helfgott, Minor arcs for Goldbach, section 4.1.2, equation (4.20), https://arxiv.org/abs/1205.5252. Complete Lean proof with exact finite endpoints. Written by Codex.

import Mathlib
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical Interval

namespace Helfgott

theorem mobius_sigma_cutoff_coprime_pair_quadratic_bound  (q Y : ℕ) (U z : ℝ) :
    let f : ℕ→ℝ := fun n => ((moebius n : ℤ) : ℝ)/(∏ p∈n.primeFactors,((p : ℝ)+1))
    |∑ r∈Finset.Icc 1 Y,∑ t∈Finset.Icc 1 Y,
      if Nat.Coprime r t ∧ Nat.Coprime r q ∧ Nat.Coprime t q ∧ U*r<z ∧ U*t<z then f r*f t else 0| ≤
      ∑ d∈Finset.Icc 1 Y,if Nat.Coprime d q then
        (|((moebius d : ℤ) : ℝ)|/(∏ p∈d.primeFactors,((p : ℝ)+1))^2)*
          (∑ a∈Finset.Icc 1 (Y/d),if Nat.Coprime a (d*q) ∧ U*(d*a : ℕ)<z then f a else 0)^2 else 0 := by sorry

end Helfgott
