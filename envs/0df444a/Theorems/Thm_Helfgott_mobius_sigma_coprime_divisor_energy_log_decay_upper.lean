-- Prove2me | Theorems.Thm_Helfgott_mobius_sigma_coprime_divisor_energy_log_decay_upper
-- name    : Helfgott.mobius_sigma_coprime_divisor_energy_log_decay_upper
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T03:55:53.256505+00:00
-- url     : https://prove2.me/theorems/02efe377-049f-4391-8230-d1550ca51610
-- title:
--   Explicit divisor-weighted Mobius square energy from reciprocal logarithmic decay
-- statement:
--   Assume the ordinary reciprocal Mobius sum satisfies $|\sum_{n\le\lfloor x\rfloor}\mu(n)/n|\le0.03/\log x$ for every $x\ge11815$. Let q,Y,L be positive integers with $L\ge11815$ and $1/2<s\le1$. Define
--   $$\sigma_\flat(n)=\prod_{p\mid n}(p+1),\qquad \Phi(u)=\sum_{n=1}^{\infty}n^{-u},$$
--   $$R_q(t)=\frac{\Phi(t+1)\Phi(2t+1)}{\Phi(3)}\prod_{p\mid q}\frac{p+1}{p+1-p^{1-t}},$$
--   $$C(u,v)=\frac{\Phi(u+v)\Phi(u+2v)\Phi(2u+v)}{\Phi(3)^2\Phi(4)},\qquad c=\frac{0.03}{\log L},\qquad P=(2L/Y)^{1-s}.$$
--   Then the complete finite divisor-weighted square energy satisfies
--   $$\sum_{\substack{d\le Y\\(d,q)=1}}\frac{|\mu(d)|}{\sigma_\flat(d)^2}\left(\sum_{\substack{r\le\lfloor Y/d\rfloor\\(r,dq)=1}}\frac{\mu(r)}{\sigma_\flat(r)}\right)^2
--   \le c^2R_q(1)^2C(1,1)+2cPR_q(1)R_q(s)C(1,s)+P^2R_q(s)^2C(s,s).$$
--   All single and coupled Euler moments, local modulus factors, squarefree identities, and finite quotient inequalities are proved. The ordinary reciprocal decay is the sole cancellation assumption. This is the weighted square sum consumed by the actual odd Vaughan integral after its strict cutoff is converted to an effective integer length.
-- source:
--   Independent explicit transfer combining exact Mobius-over-sigma and coprime positive convolutions with proved single Rankin prime factors and divisor moments. The only analytic assumption is the displayed ordinary reciprocal decay. Written by Codex.

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Topology.Algebra.InfiniteSum.Basic
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

namespace Helfgott

theorem mobius_sigma_coprime_divisor_energy_log_decay_upper
    (hdecay : ∀ x : ℝ, 11815 ≤ x →
      |∑ a∈Icc 1 ⌊x⌋₊, ((moebius a : ℤ) : ℝ)/(a : ℝ)| ≤ (3/100)/Real.log x)
    (q Y L : ℕ) (s : ℝ) (hq : 1 ≤ q) (hY : 1 ≤ Y) (hL : 11815 ≤ L)
    (hs0 : 1/2 < s) (hs1 : s ≤ 1) :
    let R : ℝ → ℝ := fun t =>
      (((∑' n : ℕ,(n : ℝ)^(-t-1))*(∑' n : ℕ,(n : ℝ)^(-2*t-1)))/
        (∑' n : ℕ,(n : ℝ)^(-3 : ℝ))) *
        (∏ p∈q.primeFactors, ((p : ℝ)+1)/((p : ℝ)+1-(p : ℝ)*(p : ℝ)^(-t)))
    let C : ℝ → ℝ → ℝ := fun u v =>
      ((∑' n : ℕ,(n : ℝ)^(-u-v))*(∑' n : ℕ,(n : ℝ)^(-u-2*v))*(∑' n : ℕ,(n : ℝ)^(-2*u-v)))/
        ((∑' n : ℕ,(n : ℝ)^(-3 : ℝ))^2*(∑' n : ℕ,(n : ℝ)^(-4 : ℝ)))
    let P : ℝ := ((2*(L : ℝ))/Y)^(1-s)
    (∑ d∈Icc 1 Y, if Nat.Coprime d q then
      |((moebius d : ℤ) : ℝ)|/(∏ p∈d.primeFactors, ((p : ℝ)+1))^2 *
        (∑ r∈Icc 1 (Y/d), if Nat.Coprime r (d*q) then
          ((moebius r : ℤ) : ℝ)/(∏ p∈r.primeFactors, ((p : ℝ)+1)) else 0)^2 else 0) ≤
      ((3/100)/Real.log (L : ℝ))^2*(R 1)^2*C 1 1 + 2*((3/100)/Real.log (L : ℝ))*P*R 1*R s*C 1 s + P^2*(R s)^2*C s s := by sorry

end Helfgott
