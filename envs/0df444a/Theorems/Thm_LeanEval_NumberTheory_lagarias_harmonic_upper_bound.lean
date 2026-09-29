-- Prove2me | Theorems.Thm_LeanEval_NumberTheory_lagarias_harmonic_upper_bound
-- name    : LeanEval.NumberTheory.lagarias_harmonic_upper_bound
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-06T02:08:05.851961+00:00
-- url     : https://prove2.me/theorems/f4378e6c-7e98-4dc2-b6a3-317524fd5feb
-- title:
--   Harmonic upper comparison (Lagarias Lemma 3.2)
-- statement:
--   Let $\gamma$ be Euler's constant. For every natural number $n\ge20$,
--
--   $$H_n+\exp(H_n)\log(H_n)\le e^\gamma n\log\log n+\frac{7n}{\log n}.$$
--
--   This unconditional upper estimate retains both the source's numerical constant and its threshold; neither is an assumed asymptotic placeholder.
-- source:
--   Jeffrey C. Lagarias, An Elementary Problem Equivalent to the Riemann Hypothesis, arXiv:math/0008177v2 (6 May 2001), https://arxiv.org/abs/math/0008177v2, p. 7, Lemma 3.2, equation (3.7).

import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

open scoped ArithmeticFunction.sigma

namespace LeanEval.NumberTheory

theorem lagarias_harmonic_upper_bound (n : ℕ) (hn : 20 ≤ n) :
    (harmonic n : ℝ) +
      Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ) ≤
      Real.exp Real.eulerMascheroniConstant * (n : ℝ) * Real.log (Real.log (n : ℝ)) +
        7 * (n : ℝ) / Real.log (n : ℝ) := by sorry

end LeanEval.NumberTheory
