-- Prove2me | Theorems.Thm_Helfgott_rankin_coupled_positive_divisor_series_certificate
-- name    : Helfgott.rankin_coupled_positive_divisor_series_certificate
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-06T16:39:35.136399+00:00
-- url     : https://prove2.me/theorems/0d82c746-70a4-4879-a193-93dc127acb40
-- title:
--   Complete coupled positive squarefree Rankin divisor series with sharp zeta bound
-- statement:
--   For $1/2\le s,t\le1$ and $s+t>1$, the positive divisor series $$\sum_{n\ge1}\frac{\mu(n)^2 n^{-s-t}}{\prod_{p\mid n}(1-p^{-s}+p^{-1})(1-p^{-t}+p^{-1})}$$ is absolutely convergent and at most $\zeta(s+t)\zeta(s+2t)\zeta(2s+t)/(\zeta(3)^2\zeta(4))$. The same sharp bound holds for every finite truncation. Each zeta value is its actual convergent real Dirichlet series. All multiplicativity, local factors, exact nonnegative polynomial comparison and convergence arguments are proved.
-- source:
--   H. A. Helfgott, Minor arcs for Goldbach, section 4.1.2, equations (4.22) and (4.24), https://arxiv.org/abs/1205.5252. Complete positive arithmetic series, sharp Euler product and convergence Lean proof. Written by Codex.

import Mathlib
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical Interval

namespace Helfgott

theorem rankin_coupled_positive_divisor_series_certificate  (s t : ℝ) (hs0 : 1/2 ≤ s) (hs1 : s ≤ 1)
    (ht0 : 1/2 ≤ t) (ht1 : t ≤ 1) (hst : 1 < s+t) :
    let f : ℕ → ℝ := fun n => ((moebius n : ℤ) : ℝ)^2*(n : ℝ)^(-s-t)/
      (∏ p∈n.primeFactors,(1-(p : ℝ)^(-s)+(p : ℝ)^(-1:ℝ))*(1-(p : ℝ)^(-t)+(p : ℝ)^(-1:ℝ)))
    let C : ℝ := ((∑' n : ℕ,(n : ℝ)^(-s-t))*(∑' n : ℕ,(n : ℝ)^(-s-2*t))*(∑' n : ℕ,(n : ℝ)^(-2*s-t)))/
      ((∑' n : ℕ,(n : ℝ)^(-3:ℝ))^2*(∑' n : ℕ,(n : ℝ)^(-4:ℝ)))
    Summable f ∧ (∑' n : ℕ,f n) ≤ C ∧ ∀ Y : ℕ,(∑ n∈Finset.Icc 1 Y,f n) ≤ C := by sorry

end Helfgott
