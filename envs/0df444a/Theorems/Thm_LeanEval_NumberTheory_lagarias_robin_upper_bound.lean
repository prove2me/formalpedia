-- Prove2me | Theorems.Thm_LeanEval_NumberTheory_lagarias_robin_upper_bound
-- name    : LeanEval.NumberTheory.lagarias_robin_upper_bound
-- status  : Open
-- author  : @xuanji
-- created : 2026-09-06T02:08:25.381502+00:00
-- url     : https://prove2.me/theorems/478d7311-75ad-4f05-a938-96500d7fff45
-- title:
--   Robin conditional upper bound (Lagarias Proposition 3.1)
-- statement:
--   Assume the Riemann hypothesis. For every natural number $n\ge5041$,
--
--   $$\sigma(n)\le e^\gamma n\log\log n.$$
--
--   Here $\gamma$ is Euler's constant. This is the non-strict formulation in Lagarias's Proposition 3.1, attributed there to Robin's Theorem 1. It is a major conditional analytic theorem to formalize, not an assumption made available for free and not a request to prove RH.
-- source:
--   Jeffrey C. Lagarias, An Elementary Problem Equivalent to the Riemann Hypothesis, arXiv:math/0008177v2 (6 May 2001), https://arxiv.org/abs/math/0008177v2, p. 6, Proposition 3.1, equation (3.1); attributed there to Robin (1984), Theorem 1.

import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

open scoped ArithmeticFunction.sigma

namespace LeanEval.NumberTheory

theorem lagarias_robin_upper_bound (hRH : RiemannHypothesis) (n : ℕ) (hn : 5041 ≤ n) :
    ((σ 1 n : ℕ) : ℝ) ≤
      Real.exp Real.eulerMascheroniConstant * (n : ℝ) * Real.log (Real.log (n : ℝ)) := by sorry

end LeanEval.NumberTheory
