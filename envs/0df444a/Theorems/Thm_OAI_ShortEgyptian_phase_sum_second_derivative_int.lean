-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_phase_sum_second_derivative_int
-- name    : OAI.ShortEgyptian.phase_sum_second_derivative_int
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:25:40.123195+00:00
-- url     : https://prove2.me/theorems/1be28cee-11a2-49b4-be3b-5d776313915d
-- title:
--   Second-derivative test for exponential sums over an arbitrary integer interval
-- statement:
--   Write $e(x)=e^{2\pi i x}$. Let $f:\mathbb{Z}\to\mathbb{R}$, let $p\le q$ be integers, and let $\lambda,A$ be real numbers with $0<\lambda\le1$ and $A\ge0$. Suppose
--   $$
--   \lambda\le f(n+2)-2f(n+1)+f(n)\le A\lambda\qquad\text{for all integers }p\le n<q.
--   $$
--   Then
--
--   $$
--   \Bigl|\sum_{n=p}^{q}e\bigl(f(n)\bigr)\Bigr|\le6A(q-p)\sqrt\lambda+\frac6{\sqrt\lambda}+6 .
--   $$
--
--   This transfers the explicit second-derivative test from sums starting at $0$ to sums over an arbitrary integer interval $[p,q]$ with $q-p+1$ terms. This is the form needed for sums of differenced phases over shortened intervals.
--
--   **Formalization Note** The sum is over `Finset.Icc p q` in the integers, and the hypothesis is required for `n ∈ Ico p q`; it involves the values $f(n)$ for $p\le n\le q+1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/IteratedDifferencing.lean#L141-L158

import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IteratedDifferencing

open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset

theorem OAI.ShortEgyptian.phase_sum_second_derivative_int (f : ℤ → ℝ) (p q : ℤ) (hpq : p ≤ q)
    {lam A : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hA : 0 ≤ A)
    (hstep : ∀ n ∈ Ico p q,
      lam ≤ (f (n + 2) - f (n + 1)) - (f (n + 1) - f n) ∧
      (f (n + 2) - f (n + 1)) - (f (n + 1) - f n) ≤ A * lam) :
    ‖∑ n ∈ Icc p q, phase (f n)‖ ≤
      6 * A * (q - p : ℤ) * Real.sqrt lam + 6 / Real.sqrt lam + 6 := by sorry
