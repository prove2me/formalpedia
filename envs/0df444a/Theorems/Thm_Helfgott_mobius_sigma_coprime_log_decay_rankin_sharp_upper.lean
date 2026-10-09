-- Prove2me | Theorems.Thm_Helfgott_mobius_sigma_coprime_log_decay_rankin_sharp_upper
-- name    : Helfgott.mobius_sigma_coprime_log_decay_rankin_sharp_upper
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T03:46:43.755568+00:00
-- url     : https://prove2.me/theorems/821f6be3-38d8-46f5-a457-29f39aa385a5
-- title:
--   Sharper coprime Mobius-over-sigma cancellation retaining the modulus Euler factors
-- statement:
--   Suppose the ordinary reciprocal Mobius sum satisfies
--   $$\left|\sum_{n\le\lfloor x\rfloor}\frac{\mu(n)}n\right|\le\frac{0.03}{\log x}\qquad(x\ge11815).$$
--   Let $q,Y,L$ be positive integers with $L\ge11815$, and let $1/2\le s\le1$. Set $\sigma_\flat(n)=\prod_{p\mid n}(p+1)$, $\Phi(u)=\sum_{n=1}^\infty n^{-u}$, and
--   $$R_q(t)=\frac{\Phi(t+1)\Phi(2t+1)}{\Phi(3)}\prod_{p\mid q}\frac{p+1}{p+1-p^{1-t}}.$$
--   Then
--   $$\left|\sum_{\substack{r\le Y\\(r,q)=1}}\frac{\mu(r)}{\sigma_\flat(r)}\right|
--   \le\frac{0.03}{\log L}R_q(1)+\left(\frac LY\right)^{1-s}R_q(s).$$
--   The modulus factor retains the coprime restriction in the multiplicative moment. The first term transfers logarithmic cancellation through the exact positive convolutions. The second controls quotients below L using the unconditional unit bound and a Rankin tail. All series and prime-factor estimates used by the transfer are proved. This is a quantitative input for the actual Vaughan Type II coefficient energy.
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

theorem mobius_sigma_coprime_log_decay_rankin_sharp_upper
    (hdecay : ∀ x : ℝ, 11815 ≤ x →
      |∑ a ∈ Icc 1 ⌊x⌋₊, ((moebius a : ℤ) : ℝ)/(a : ℝ)| ≤
        (3/100)/Real.log x)
    (q Y L : ℕ) (s : ℝ) (hq : 1 ≤ q) (hY : 1 ≤ Y) (hL : 11815 ≤ L)
    (hs0 : 1/2 ≤ s) (hs1 : s ≤ 1) :
    let R : ℝ → ℝ := fun t =>
      (((∑' n : ℕ, (n : ℝ)^(-t-1))*(∑' n : ℕ, (n : ℝ)^(-2*t-1)))/
        (∑' n : ℕ, (n : ℝ)^(-3 : ℝ))) *
      (∏ p ∈ q.primeFactors, ((p : ℝ)+1)/((p : ℝ)+1-(p : ℝ)*(p : ℝ)^(-t)))
    |∑ r ∈ Icc 1 Y, if Nat.Coprime r q then
      ((moebius r : ℤ) : ℝ)/(∏ p ∈ r.primeFactors, ((p : ℝ)+1)) else 0| ≤
      ((3/100)/Real.log (L : ℝ))*R 1 + ((L : ℝ)/Y)^(1-s)*R s := by sorry

end Helfgott
