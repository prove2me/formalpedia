-- Prove2me | Theorems.Thm_HighResODE_NAGC_lemma_4_3
-- name    : HighResODE.NAGC.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:26:05.026809+00:00
-- url     : https://prove2.me/theorems/bf22e190-cc7f-4e4a-9e81-5ce10f49fc2d
-- title:
--   Lemma 4.3, p. 25 — E(k + 1) − E(k) ≤ −(s²((k + 3)(k − 1) − Ls(k + 3)(k + 1))/2)‖∇f(xₖ₊₁)‖²
-- statement:
--   Let $f\in\mathcal F^1_L(\mathbb R^n)$, let $x^\star$ be a minimizer of $f$, let $0<s\le 1/(3L)$, and let $(x_k,y_k)$ be a run of NAG-C with step size $s$. With $\mathcal E$ the Lyapunov function (4.6), for every $k\ge0$
--   $$
--   \mathcal E(k+1)-\mathcal E(k)\le-\frac{s^2\bigl((k+3)(k-1)-Ls(k+3)(k+1)\bigr)}{2}\,\|\nabla f(x_{k+1})\|^2 .
--   $$
--
--   For $k\ge2$ the coefficient on the right is non-positive under $s\le1/(3L)$, so $\mathcal E$ decreases from $k=2$ on, by an amount proportional to $k^2s^2\|\nabla f(x_{k+1})\|^2$; this quadratic weight is the source of the inverse cubic rate for the squared gradient norm.
--
--   **Formalization Note** The factor $k-1$ is a real number (it equals $-1$ at $k=0$, where the bound is positive and still asserted). The minimizer $x^\star$ is a hypothesis: the paper presupposes that $f$ has a minimizer.
-- source:
--   Shi, Du, Jordan & Su, Understanding the Acceleration Phenomenon via High-Resolution Differential Equations, arXiv:1810.08907v3, p. 25, Lemma 4.3

import Mathlib
import Definitions.Def_HighResODE_NAGC_Setting

namespace HighResODE.NAGC

open scoped InnerProductSpace

/-- Lemma 4.3, p. 25. The factor `k − 1` is real (it equals `−1` at `k = 0`). -/
theorem lemma_4_3 {n : ℕ} (f : HighResODE.NAGSC.E n → ℝ) (L s : ℝ) (hf : HighResODE.NAGSC.IsF1 f L) (xs : HighResODE.NAGSC.E n)
    (hmin : ∀ z : HighResODE.NAGSC.E n, f xs ≤ f z) (hs : 0 < s) (hsL : s ≤ 1 / (3 * L))
    (x y : ℕ → HighResODE.NAGSC.E n) (hrun : IsNAGC f s x y) :
    ∀ k : ℕ, lyap f s xs x (k + 1) - lyap f s xs x k
      ≤ -(s ^ 2 * (((k : ℝ) + 3) * ((k : ℝ) - 1) - L * s * ((k : ℝ) + 3) * ((k : ℝ) + 1)) / 2)
          * ‖gradient f (x (k + 1))‖ ^ 2 := by sorry

end HighResODE.NAGC
