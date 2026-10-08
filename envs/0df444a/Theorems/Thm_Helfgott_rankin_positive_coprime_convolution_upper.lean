-- Prove2me | Theorems.Thm_Helfgott_rankin_positive_coprime_convolution_upper
-- name    : Helfgott.rankin_positive_coprime_convolution_upper
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-06T16:39:40.953984+00:00
-- url     : https://prove2.me/theorems/72ff56ce-18e5-46c1-a626-58bc3bc947ef
-- title:
--   Sharp finite positive coprime Rankin convolution bound
-- statement:
--   For $q\ge1$, $Y\ge0$ and $1/2\le s\le1$, $$\sum_{e\le Y\atop(e,q)=1}\frac{\mu(e)^2}{e^s\sigma(e)}\sum_{b\le Y/e\atop p\mid b\Rightarrow p\mid eq}b^{-s}\le\frac{\zeta(s+1)\zeta(2s+1)}{\zeta(3)}\prod_{p\mid q}(1-p^{-s})^{-1},$$ where $\sigma(e)=\prod_{p\mid e}(p+1)$. Every finite endpoint and arbitrary prime power in the inner sum is retained. This is the uniform positive Rankin moment for the coprime Mobius-to-Mobius-over-sigma convolution.
-- source:
--   H. A. Helfgott, Minor arcs for Goldbach, section 4.1.2, equations (4.22) and (4.23), https://arxiv.org/abs/1205.5252. Complete positive arithmetic series, sharp Euler product and convergence Lean proof. Written by Codex.

import Mathlib
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical Interval

namespace Helfgott

theorem rankin_positive_coprime_convolution_upper  (q Y : ℕ) (hq : 1 ≤ q) (s : ℝ)
    (hs0 : 1/2 ≤ s) (hs1 : s ≤ 1) :
    (∑ e∈Finset.Icc 1 Y,if Nat.Coprime e q then
      (((moebius e : ℤ) : ℝ)^2*(e : ℝ)^(-s)/(∏ p∈e.primeFactors,((p : ℝ)+1)))*
        (∑ b∈Finset.Icc 1 (Y/e),if (∀ p∈b.primeFactors,p∣e*q) then (b : ℝ)^(-s) else 0) else 0) ≤
      (((∑' n : ℕ,(n : ℝ)^(-s-1))*(∑' n : ℕ,(n : ℝ)^(-2*s-1)))/(∑' n : ℕ,(n : ℝ)^(-3:ℝ)))*
        (∏ p∈q.primeFactors,(1-(p : ℝ)^(-s))⁻¹) := by sorry

end Helfgott
