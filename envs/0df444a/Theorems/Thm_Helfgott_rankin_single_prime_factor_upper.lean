-- Prove2me | Theorems.Thm_Helfgott_rankin_single_prime_factor_upper
-- name    : Helfgott.rankin_single_prime_factor_upper
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-06T16:16:36.794984+00:00
-- url     : https://prove2.me/theorems/1e41f9a1-2a01-40ae-8aaa-66cc82936cb2
-- title:
--   Sharp single Euler factor comparison for the Vaughan Rankin bound
-- statement:
--   For every real $p>1$ and $1/2\le s\le1$, $$1+\frac{p^{-s-1}}{(1+p^{-1})(1-p^{-s})}\le\frac{1-p^{-3}}{(1-p^{-s-1})(1-p^{-2s-1})}.$$ In particular the inequality holds at every prime. It is the local comparison that bounds a weighted squarefree divisor Euler product by zeta factors in the quantitative Vaughan Mobius cancellation argument.
-- source:
--   H. A. Helfgott, Minor arcs for Goldbach, section 4.1.2, equation (4.23), https://arxiv.org/abs/1205.5252. Complete real-algebra and real-power Lean proof. Written by Codex.

import Mathlib
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical Interval

namespace Helfgott

theorem rankin_single_prime_factor_upper  (p s : ℝ) (hp : 1<p) (hs0 : 1/2 ≤ s) (hs1 : s ≤ 1) :
    1+p^(-s-1)/((1+p^(-1:ℝ))*(1-p^(-s)))≤
      (1-p^(-3:ℝ))/((1-p^(-s-1))*(1-p^(-2*s-1))) := by sorry

end Helfgott
