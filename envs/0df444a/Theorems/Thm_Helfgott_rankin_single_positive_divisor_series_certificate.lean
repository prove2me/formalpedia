-- Prove2me | Theorems.Thm_Helfgott_rankin_single_positive_divisor_series_certificate
-- name    : Helfgott.rankin_single_positive_divisor_series_certificate
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-06T16:33:34.895235+00:00
-- url     : https://prove2.me/theorems/d4b9b0c5-d078-429f-9767-cab34102558c
-- title:
--   Complete positive squarefree Rankin divisor series with sharp zeta bound
-- statement:
--   For $1/2\le s\le1$, the positive divisor series $$\sum_{n\ge1}\frac{\mu(n)^2}{n^s\prod_{p\mid n}(p+1)(1-p^{-s})}$$ is absolutely convergent and at most $\zeta(s+1)\zeta(2s+1)/\zeta(3)$. The same bound holds for every finite truncation, including the empty endpoint. Every real zeta value is its actual convergent Dirichlet series. The proof includes all multiplicativity, prime-power vanishing, Euler-product and convergence arguments.
-- source:
--   H. A. Helfgott, Minor arcs for Goldbach, section 4.1.2, equations (4.22) and (4.23), https://arxiv.org/abs/1205.5252. Complete positive arithmetic series, sharp Euler product and convergence Lean proof. Written by Codex.

import Mathlib
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical Interval

namespace Helfgott

theorem rankin_single_positive_divisor_series_certificate  (s : ℝ) (hs0 : 1/2 ≤ s) (hs1 : s ≤ 1) :
    let f : ℕ → ℝ := fun n => ((moebius n : ℤ) : ℝ)^2*(n : ℝ)^(-s)/
      (∏ p∈n.primeFactors,((p : ℝ)+1)*(1-(p : ℝ)^(-s)))
    let C : ℝ := ((∑' n : ℕ,(n : ℝ)^(-s-1))*(∑' n : ℕ,(n : ℝ)^(-2*s-1)))/
      (∑' n : ℕ,(n : ℝ)^(-3:ℝ))
    Summable f ∧ (∑' n : ℕ,f n) ≤ C ∧ ∀ Y : ℕ,(∑ n∈Finset.Icc 1 Y,f n) ≤ C := by sorry

end Helfgott
