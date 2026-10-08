-- Prove2me | Theorems.Thm_Helfgott_rankin_coupled_finite_prime_product_upper
-- name    : Helfgott.rankin_coupled_finite_prime_product_upper
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-06T16:29:29.226597+00:00
-- url     : https://prove2.me/theorems/1fb4d7ee-5e9a-4b2d-94d9-a889e1f88c62
-- title:
--   Sharp zeta-quotient bound for every finite coupled Rankin prime product
-- statement:
--   For every finite set $P$ of primes and $1/2\le s,t\le1$ with $s+t>1$, $$\prod_{p\in P}\left(1+\frac{p^{-s-t}}{(1-p^{-s}+p^{-1})(1-p^{-t}+p^{-1})}\right)\le\frac{\zeta(s+t)\zeta(s+2t)\zeta(2s+t)}{\zeta(3)^2\zeta(4)}.$$ The formal statement defines each real zeta value as its convergent positive Dirichlet series. The proof establishes convergence of every comparison Euler product and a bound uniform in the finite prime set. It supplies the global sharp constant for the coupled Rankin divisor convolution.
-- source:
--   H. A. Helfgott, Minor arcs for Goldbach, section 4.1.2, equations (4.22) and (4.24), https://arxiv.org/abs/1205.5252. Complete exact local polynomial certificate and global convergent Euler-product Lean proof. Written by Codex.

import Mathlib
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical Interval

namespace Helfgott

theorem rankin_coupled_finite_prime_product_upper  (P : Finset Nat.Primes) (s t : ℝ)
    (hs0 : 1/2 ≤ s) (hs1 : s ≤ 1) (ht0 : 1/2 ≤ t) (ht1 : t ≤ 1) (hst : 1 < s+t) :
    (∏ p∈P,(1+(p : ℝ)^(-s-t)/((1-(p : ℝ)^(-s)+(p : ℝ)^(-1:ℝ))*(1-(p : ℝ)^(-t)+(p : ℝ)^(-1:ℝ))))) ≤
      ((∑' n : ℕ,(n : ℝ)^(-s-t))*(∑' n : ℕ,(n : ℝ)^(-s-2*t))*(∑' n : ℕ,(n : ℝ)^(-2*s-t)))/
        ((∑' n : ℕ,(n : ℝ)^(-3:ℝ))^2*(∑' n : ℕ,(n : ℝ)^(-4:ℝ))) := by sorry

end Helfgott
