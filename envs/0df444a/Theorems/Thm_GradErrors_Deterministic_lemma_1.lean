-- Prove2me | Theorems.Thm_GradErrors_Deterministic_lemma_1
-- name    : GradErrors.Deterministic.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T16:29:19.127282+00:00
-- url     : https://prove2.me/theorems/b8681f01-381e-448c-9db5-da40f7c7f284
-- title:
--   Lemma 1, p. 629 — if Y_{t+1} ≤ Y_t − W_t + Z_t with W_t ≥ 0 and Σ Z_t convergent, then Y_t → −∞ or Y_t converges and Σ W_t < ∞
-- statement:
--   Let $(Y_t)$, $(W_t)$, $(Z_t)$ be real sequences with $W_t\ge 0$ for all $t$, such that
--   $$Y_{t+1}\le Y_t-W_t+Z_t,\qquad t=0,1,\dots,$$
--   and such that the partial sums $\sum_{t=0}^{T}Z_t$ converge to a finite limit as $T\to\infty$. Then either $Y_t\to-\infty$, or else $Y_t$ converges to a finite value and
--   $$\sum_{t=0}^{\infty}W_t<\infty.$$
--
--   This is the deterministic counterpart of the Robbins–Siegmund supermartingale lemma. In the paper it turns the one-step descent inequality (2.5) of a gradient method into the dichotomy "$f(x_t)\to-\infty$ or $f(x_t)$ converges, with $\sum_t\gamma_t\|\nabla f(x_t)\|^2<\infty$".
--
--   **Formalization Note** Convergence of $\sum_t Z_t$ is stated as convergence of the partial sums, not as Lean's `Summable`, which for real sequences means absolute convergence; $Z_t$ may change sign and the series may converge only conditionally. For the nonnegative $W_t$ the conclusion `Summable W` is exactly $\sum_t W_t<\infty$.
-- source:
--   Bertsekas and Tsitsiklis, Gradient Convergence in Gradient Methods with Errors, SIAM J. Optim. 10 (2000), https://doi.org/10.1137/S1052623497331063, p. 629, Lemma 1

import Mathlib

open Filter Topology NNReal InnerProductSpace

namespace GradErrors.Deterministic

theorem lemma_1 (Y W Z : ℕ → ℝ) (hW : ∀ t, 0 ≤ W t)
    (hrec : ∀ t, Y (t + 1) ≤ Y t - W t + Z t)
    (hZ : ∃ S : ℝ, Tendsto (fun T => ∑ t ∈ Finset.range (T + 1), Z t) atTop (𝓝 S)) :
    Tendsto Y atTop atBot ∨ ((∃ y : ℝ, Tendsto Y atTop (𝓝 y)) ∧ Summable W) := by sorry

end GradErrors.Deterministic
