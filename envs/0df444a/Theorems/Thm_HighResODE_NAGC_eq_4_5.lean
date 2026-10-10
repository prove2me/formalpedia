-- Prove2me | Theorems.Thm_HighResODE_NAGC_eq_4_5
-- name    : HighResODE.NAGC.eq_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:26:23.94387+00:00
-- url     : https://prove2.me/theorems/c4789933-fd20-4b36-abe5-4e1fc144f21b
-- title:
--   (4.5), p. 25 — phase-space representation of NAG-C with v₀ = −√s∇f(x₀)
-- statement:
--   Let $s>0$, let $f:\mathbb R^n\to\mathbb R$, and let $(x_k,y_k)_{k\ge0}$ be a run of NAG-C with step size $s$ and velocity $v_k=(x_{k+1}-x_k)/\sqrt s$. Then for every $k\ge1$
--   $$
--   x_k-x_{k-1}=\sqrt s\,v_{k-1},\qquad v_k-v_{k-1}=-\frac3k v_k-\sqrt s\bigl(\nabla f(x_k)-\nabla f(x_{k-1})\bigr)-\Bigl(1+\frac3k\Bigr)\sqrt s\,\nabla f(x_k),
--   $$
--   and the initial velocity is $v_0=-\sqrt s\,\nabla f(x_0)$.
--
--   This rewrites the two-sequence algorithm as a first-order system in position and velocity, the discrete counterpart of the high-resolution ODE of NAG-C; it is the form in which the Lyapunov function (4.6) is analysed.
--
--   **Formalization Note** The identities are stated with $k+1$ in place of the paper's $k$, for every $k\ge0$, so no natural-number subtraction occurs. Neither convexity nor smoothness of $f$ is assumed: the identities hold for any $f$, which is stronger than the page needs.
-- source:
--   Shi, Du, Jordan & Su, Understanding the Acceleration Phenomenon via High-Resolution Differential Equations, arXiv:1810.08907v3, p. 25, (4.5)

import Mathlib
import Definitions.Def_HighResODE_NAGC_Setting

namespace HighResODE.NAGC

open scoped InnerProductSpace

/-- (4.5), p. 25 (stated with `k + 1` in place of the page's `k`): the phase-space
representation of NAG-C and its initial velocity. -/
theorem eq_4_5 {n : ℕ} (f : HighResODE.NAGSC.E n → ℝ) (s : ℝ) (hs : 0 < s) (x y : ℕ → HighResODE.NAGSC.E n) (hrun : IsNAGC f s x y) :
    (∀ k : ℕ, x (k + 1) - x k = Real.sqrt s • HighResODE.NAGSC.vel s x k) ∧
    (∀ k : ℕ, HighResODE.NAGSC.vel s x (k + 1) - HighResODE.NAGSC.vel s x k
        = -(3 / ((k : ℝ) + 1)) • HighResODE.NAGSC.vel s x (k + 1)
          - Real.sqrt s • (gradient f (x (k + 1)) - gradient f (x k))
          - ((1 + 3 / ((k : ℝ) + 1)) * Real.sqrt s) • gradient f (x (k + 1))) ∧
    HighResODE.NAGSC.vel s x 0 = -(Real.sqrt s) • gradient f (x 0) := by sorry

end HighResODE.NAGC
