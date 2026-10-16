-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_phase_sum_second_derivative_sqrt
-- name    : OAI.ShortEgyptian.phase_sum_second_derivative_sqrt
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:23:11.474316+00:00
-- url     : https://prove2.me/theorems/496c6405-68b5-404f-89dc-98a5cbf14c1b
-- title:
--   Van der Corput's second-derivative test with explicit constants
-- statement:
--   Write $e(x)=e^{2\pi i x}$ for $x\in\mathbb{R}$. Let $f:\mathbb{N}\to\mathbb{R}$ and $N\in\mathbb{N}$, and let $\lambda,A$ be real numbers with $0<\lambda\le1$ and $A\ge0$. Suppose that the second differences $\Delta^2f(n)=f(n+2)-2f(n+1)+f(n)$ satisfy
--   $$
--   \lambda\le\Delta^2f(n)\le A\lambda\qquad\text{for all integers }0\le n<N.
--   $$
--   Then
--
--   $$
--   \Bigl|\sum_{n=0}^{N}e\bigl(f(n)\bigr)\Bigr|\le6AN\sqrt\lambda+\frac6{\sqrt\lambda}+6 .
--   $$
--
--   This is a discrete version of van der Corput's second-derivative test, $\sum_n e(f(n))\ll AN\lambda^{1/2}+\lambda^{-1/2}$, with explicit constants. The second differences must be positive and comparable to $\lambda$, with ratio at most $A$. It is the estimate applied at the end of repeated van der Corput differencing.
--
--   **Formalization Note** The sum runs over `range (N + 1)`, i.e. $n=0,\dots,N$, and $e(x)$ is `phase x`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/IntervalDifferencing.lean#L17-L38

import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing

open OAI OAI.ShortEgyptian
universe uι uκ uM
open scoped BigOperators
open Finset

theorem OAI.ShortEgyptian.phase_sum_second_derivative_sqrt (f : ℕ → ℝ) (N : ℕ) {lam A : ℝ}
    (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hA : 0 ≤ A)
    (hstep : ∀ n < N,
      lam ≤ (f (n + 2) - f (n + 1)) - (f (n + 1) - f n) ∧
      (f (n + 2) - f (n + 1)) - (f (n + 1) - f n) ≤ A * lam) :
    ‖∑ n ∈ range (N + 1), phase (f n)‖ ≤
      6 * A * N * Real.sqrt lam + 6 / Real.sqrt lam + 6 := by sorry
