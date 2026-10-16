-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_phase_sum_second_derivative
-- name    : OAI.ShortEgyptian.phase_sum_second_derivative
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:20:35.687997+00:00
-- url     : https://prove2.me/theorems/9f189bf6-e59d-47df-a53a-d495abba119e
-- title:
--   Discrete second-derivative bound for exponential sums with a free parameter $\beta$
-- statement:
--   Write $e(x)=e^{2\pi i x}$ for $x\in\mathbb{R}$. Let $f:\mathbb{N}\to\mathbb{R}$ and $N\in\mathbb{N}$, and let $\lambda,\Lambda,\beta$ be real numbers with $\lambda>0$ and $\beta>0$. Write $\Delta^2f(n)=f(n+2)-2f(n+1)+f(n)$ for the second difference, and assume
--
--   $$
--   \lambda\le\Delta^2f(n)\le\Lambda\qquad\text{for all integers }0\le n<N.
--   $$
--
--   Then
--
--   $$
--   \Bigl|\sum_{n=0}^{N}e\bigl(f(n)\bigr)\Bigr|\le(\Lambda N+2)\Bigl(\frac{2\beta}{\lambda}+\frac1\beta+3\Bigr).
--   $$
--
--   This is a discrete form of van der Corput's second-derivative test that still contains a free parameter $\beta$, to be optimized in applications. With $\Lambda=A\lambda$, $\beta=\sqrt\lambda$ and $\lambda\le1$ it yields the classical shape $O\bigl(AN\sqrt\lambda+1/\sqrt\lambda+1\bigr)$.
--
--   **Formalization Note** The second difference is written `(f (n + 2) - f (n + 1)) - (f (n + 1) - f n)` and $e(x)$ is `phase x`. No sign condition on $\Lambda$ is imposed; when $N\ge1$ the hypothesis forces $\lambda\le\Lambda$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/SecondDerivative.lean#L183-L225

import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative

open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset

theorem OAI.ShortEgyptian.phase_sum_second_derivative (f : ℕ → ℝ) (N : ℕ) {lam Λ β : ℝ}
    (hlam : 0 < lam) (hβ : 0 < β)
    (hstep : ∀ n < N,
      lam ≤ (f (n + 2) - f (n + 1)) - (f (n + 1) - f n) ∧
      (f (n + 2) - f (n + 1)) - (f (n + 1) - f n) ≤ Λ) :
    ‖∑ n ∈ range (N + 1), phase (f n)‖ ≤
      (Λ * N + 2) * (2 * β / lam + 1 / β + 3) := by sorry
