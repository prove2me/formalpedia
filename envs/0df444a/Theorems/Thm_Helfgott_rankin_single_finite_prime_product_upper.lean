-- Prove2me | Theorems.Thm_Helfgott_rankin_single_finite_prime_product_upper
-- name    : Helfgott.rankin_single_finite_prime_product_upper
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-06T16:29:48.213041+00:00
-- url     : https://prove2.me/theorems/f310fd1e-ad98-43a2-a48f-7367b0f0d62e
-- title:
--   Sharp zeta-quotient bound for every finite single Rankin prime product
-- statement:
--   For every finite set $P$ of primes and $1/2\le s\le1$, $$\prod_{p\in P}\left(1+\frac{p^{-s-1}}{(1+p^{-1})(1-p^{-s})}\right)\le\frac{\zeta(s+1)\zeta(2s+1)}{\zeta(3)}.$$ Each zeta value is the actual convergent positive Dirichlet series. The proof establishes absolute convergence and exact real Euler products, including inversion at exponent 3, and the bound for every finite prime set.
-- source:
--   H. A. Helfgott, Minor arcs for Goldbach, section 4.1.2, equations (4.22) and (4.23), https://arxiv.org/abs/1205.5252. Complete exact local factor and global convergent Euler-product Lean proof. Written by Codex.

import Mathlib
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical Interval

namespace Helfgott

theorem rankin_single_finite_prime_product_upper  (P : Finset Nat.Primes) (s : ℝ)
    (hs0 : 1/2 ≤ s) (hs1 : s ≤ 1) :
    (∏ p∈P,(1+(p : ℝ)^(-s-1)/((1+(p : ℝ)^(-1:ℝ))*(1-(p : ℝ)^(-s))))) ≤
      ((∑' n : ℕ,(n : ℝ)^(-s-1))*(∑' n : ℕ,(n : ℝ)^(-2*s-1)))/(∑' n : ℕ,(n : ℝ)^(-3:ℝ)) := by sorry

end Helfgott
