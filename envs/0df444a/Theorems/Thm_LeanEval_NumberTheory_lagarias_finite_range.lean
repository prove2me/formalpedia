-- Prove2me | Theorems.Thm_LeanEval_NumberTheory_lagarias_finite_range
-- name    : LeanEval.NumberTheory.lagarias_finite_range
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-06T02:08:15.888813+00:00
-- url     : https://prove2.me/theorems/a9817102-7f53-4786-9a7d-662af06c137a
-- title:
--   Finite range and equality case through 5040
-- statement:
--   For each integer $1\le n\le5040$, let $\sigma(n)$ be the sum of its positive divisors. Then
--
--   $$\sigma(n)\le H_n+\exp(H_n)\log(H_n),$$
--
--   and equality holds if and only if $n=1$. This is the bounded verification reported in the proof of Theorem 1.1, not the universal criterion. Its formal proof must certify the real exponential and logarithm comparisons; floating-point evidence alone is insufficient.
-- source:
--   Jeffrey C. Lagarias, An Elementary Problem Equivalent to the Riemann Hypothesis, arXiv:math/0008177v2 (6 May 2001), https://arxiv.org/abs/math/0008177v2, p. 8, proof of Theorem 1.1, finite verification (unnumbered).

import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

open scoped ArithmeticFunction.sigma

namespace LeanEval.NumberTheory

theorem lagarias_finite_range (n : ℕ) (hn : 0 < n) (hbound : n ≤ 5040) :
    (((σ 1 n : ℕ) : ℝ) ≤ (harmonic n : ℝ) +
      Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ)) ∧
      ((((σ 1 n : ℕ) : ℝ) = (harmonic n : ℝ) +
      Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ)) ↔ n = 1) := by sorry

end LeanEval.NumberTheory
