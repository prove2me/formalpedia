-- Prove2me | Theorems.Thm_HighResODE_NAGC_eq_4_14
-- name    : HighResODE.NAGC.eq_4_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:26:23.024581+00:00
-- url     : https://prove2.me/theorems/d023e9a6-8e9a-40cd-92ec-b16c7d9236ae
-- title:
--   (4.14), p. 27 — exact identity for E(k + 1) − E(k) along NAG-C
-- statement:
--   Let $s>0$, $f:\mathbb R^n\to\mathbb R$, $x^\star\in\mathbb R^n$, and let $(x_k,y_k)$ be a run of NAG-C with step size $s$, velocity $v_k$ and Lyapunov function $\mathcal E$ of (4.6). Then for every $k\ge0$
--   $$
--   \begin{aligned}
--   \mathcal E(k+1)-\mathcal E(k)={}&s(k+3)(k+1)\bigl(f(x_{k+1})-f(x_k)\bigr)-s^{3/2}(k+3)(k+4)\langle\nabla f(x_{k+1}),v_{k+1}\rangle\\
--   &+s(2k+5)\bigl(f(x_{k+1})-f(x^\star)\bigr)-s(2k+6)\langle\nabla f(x_{k+1}),x_{k+1}-x^\star\rangle\\
--   &-\frac{s^2(k+3)(3k+7)}{2}\|\nabla f(x_{k+1})\|^2 .
--   \end{aligned}
--   $$
--
--   This is the exact one-step change of the Lyapunov function; Lemma 4.3 follows from it by applying convexity and $L$-smoothness to the function-value differences.
--
--   **Formalization Note** $s^{3/2}$ is the real power `s ^ ((3 : ℝ) / 2)`. The identity is algebraic: no property of $f$ or of $x^\star$ is assumed.
-- source:
--   Shi, Du, Jordan & Su, Understanding the Acceleration Phenomenon via High-Resolution Differential Equations, arXiv:1810.08907v3, p. 27, (4.14), proof of Lemma 4.3

import Mathlib
import Definitions.Def_HighResODE_NAGC_Setting

namespace HighResODE.NAGC

open scoped InnerProductSpace

/-- (4.14), p. 27: the exact identity for `E(k + 1) − E(k)` along NAG-C. -/
theorem eq_4_14 {n : ℕ} (f : HighResODE.NAGSC.E n → ℝ) (s : ℝ) (hs : 0 < s) (x y : ℕ → HighResODE.NAGSC.E n) (hrun : IsNAGC f s x y) (xs : HighResODE.NAGSC.E n) (k : ℕ) :
    lyap f s xs x (k + 1) - lyap f s xs x k
      = s * ((k : ℝ) + 3) * ((k : ℝ) + 1) * (f (x (k + 1)) - f (x k))
        - s ^ ((3 : ℝ) / 2) * ((k : ℝ) + 3) * ((k : ℝ) + 4)
            * ⟪gradient f (x (k + 1)), HighResODE.NAGSC.vel s x (k + 1)⟫_ℝ
        + s * (2 * (k : ℝ) + 5) * (f (x (k + 1)) - f xs)
        - s * (2 * (k : ℝ) + 6) * ⟪gradient f (x (k + 1)), x (k + 1) - xs⟫_ℝ
        - s ^ 2 * ((k : ℝ) + 3) * (3 * (k : ℝ) + 7) / 2 * ‖gradient f (x (k + 1))‖ ^ 2 := by sorry

end HighResODE.NAGC
