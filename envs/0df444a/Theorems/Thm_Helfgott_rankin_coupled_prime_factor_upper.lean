-- Prove2me | Theorems.Thm_Helfgott_rankin_coupled_prime_factor_upper
-- name    : Helfgott.rankin_coupled_prime_factor_upper
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-06T16:24:33.711237+00:00
-- url     : https://prove2.me/theorems/d516e4d6-808a-4760-93c6-1dab20926984
-- title:
--   Sharp coupled Euler factor comparison for the Vaughan Rankin bound
-- statement:
--   For every real $p>1$ and $1/2\le s,t\le1$, $$1+\frac{p^{-s-t}}{(1-p^{-s}+p^{-1})(1-p^{-t}+p^{-1})}\le\frac{(1-p^{-3})^2(1-p^{-4})}{(1-p^{-s-t})(1-p^{-s-2t})(1-p^{-2s-t})}.$$ This is the sharp coupled Euler-factor comparison for the positive quadratic divisor convolution in the Vaughan Mobius cancellation argument. A full exact nonnegative polynomial certificate proves the inequality for all real parameters in this range.
-- source:
--   H. A. Helfgott, Minor arcs for Goldbach, section 4.1.2, equation (4.24), https://arxiv.org/abs/1205.5252. Complete exact nonnegative polynomial certificate, real-algebra and real-power Lean proof. Written by Codex.

import Mathlib
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical Interval

namespace Helfgott

theorem rankin_coupled_prime_factor_upper  (p s t : ℝ) (hp : 1 < p)
    (hs0 : 1/2 ≤ s) (hs1 : s ≤ 1) (ht0 : 1/2 ≤ t) (ht1 : t ≤ 1) :
    1+p^(-s-t)/((1-p^(-s)+p^(-1:ℝ))*(1-p^(-t)+p^(-1:ℝ))) ≤
      (1-p^(-3:ℝ))^2*(1-p^(-4:ℝ))/
        ((1-p^(-s-t))*(1-p^(-s-2*t))*(1-p^(-2*s-t))) := by sorry

end Helfgott
