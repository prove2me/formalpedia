-- Prove2me | Theorems.Thm_LeanEval_NumberTheory_lagarias_robin_oscillation
-- name    : LeanEval.NumberTheory.lagarias_robin_oscillation
-- status  : Open
-- author  : @xuanji
-- created : 2026-09-06T02:08:37.365603+00:00
-- url     : https://prove2.me/theorems/82d05676-a09d-4ce7-aaba-8ff73c958484
-- title:
--   Robin oscillation under failure of RH (Lagarias Proposition 3.2)
-- statement:
--   Assume that the Riemann hypothesis is false. There exist fixed real constants $\beta,C$ with $0<\beta<1/2$ and $C>0$ such that arbitrarily large integers $n\ge3$ satisfy
--
--   $$\sigma(n)\ge e^\gamma n\log\log n+\frac{Cn\log\log n}{(\log n)^\beta}.$$
--
--   The same constants work for all cutoffs: for every natural number $N$, such an $n\ge N$ exists. This is the infinite-set statement of Proposition 3.2 with the finitely many indices below 3 removed, so the denominator uses a positive logarithm and an actual real power. It is a substantial oscillation theorem, not merely the assertion that Robin's inequality has a counterexample.
-- source:
--   Jeffrey C. Lagarias, An Elementary Problem Equivalent to the Riemann Hypothesis, arXiv:math/0008177v2 (6 May 2001), https://arxiv.org/abs/math/0008177v2, p. 6, Proposition 3.2, equation (3.2); attributed there to Robin (1984), §4, Proposition 1. Infinite set of indices expressed as unboundedness in ℕ, with finitely many n < 3 excluded.

import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

open scoped ArithmeticFunction.sigma

namespace LeanEval.NumberTheory

theorem lagarias_robin_oscillation (hRH : ¬ RiemannHypothesis) :
    ∃ β C : ℝ, 0 < β ∧ β < 1 / 2 ∧ 0 < C ∧
      ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ 3 ≤ n ∧
        Real.exp Real.eulerMascheroniConstant * (n : ℝ) * Real.log (Real.log (n : ℝ)) +
            C * (n : ℝ) * Real.log (Real.log (n : ℝ)) /
              Real.rpow (Real.log (n : ℝ)) β ≤
          ((σ 1 n : ℕ) : ℝ) := by sorry

end LeanEval.NumberTheory
