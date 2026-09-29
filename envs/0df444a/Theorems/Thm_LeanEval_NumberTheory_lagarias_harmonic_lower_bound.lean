-- Prove2me | Theorems.Thm_LeanEval_NumberTheory_lagarias_harmonic_lower_bound
-- name    : LeanEval.NumberTheory.lagarias_harmonic_lower_bound
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-06T02:07:53.412714+00:00
-- url     : https://prove2.me/theorems/9f88f059-0619-4575-b553-44d11fa60d73
-- title:
--   Harmonic lower comparison (Lagarias Lemma 3.1)
-- statement:
--   Let $\gamma$ be Euler's constant and $H_n$ the $n$th harmonic number. For every natural number $n\ge3$,
--
--   $$e^\gamma n\log\log n\le \exp(H_n)\log(H_n).$$
--
--   This is an unconditional lower comparison between the elementary harmonic expression and the classical divisor-sum scale.
-- source:
--   Jeffrey C. Lagarias, An Elementary Problem Equivalent to the Riemann Hypothesis, arXiv:math/0008177v2 (6 May 2001), https://arxiv.org/abs/math/0008177v2, pp. 6–7, Lemma 3.1, equation (3.3).

import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

open scoped ArithmeticFunction.sigma

namespace LeanEval.NumberTheory

theorem lagarias_harmonic_lower_bound (n : ℕ) (hn : 3 ≤ n) :
    Real.exp Real.eulerMascheroniConstant * (n : ℝ) * Real.log (Real.log (n : ℝ)) ≤
      Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ) := by sorry

end LeanEval.NumberTheory
