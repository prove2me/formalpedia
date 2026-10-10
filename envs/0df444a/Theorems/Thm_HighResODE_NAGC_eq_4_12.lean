-- Prove2me | Theorems.Thm_HighResODE_NAGC_eq_4_12
-- name    : HighResODE.NAGC.eq_4_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:26:03.827196+00:00
-- url     : https://prove2.me/theorems/ec0a96a9-a5d3-4d4a-ba40-681db306fd79
-- title:
--   (4.12), p. 27 — f(xₖ) − f(x⋆) ≤ E(k)/(s(k + 3)(k + 1)) ≤ E(2)/(s(k + 3)(k + 1)) ≤ 119‖x₀ − x⋆‖²/(s(k + 1)²), k ≥ 2
-- statement:
--   Let $f\in\mathcal F^1_L(\mathbb R^n)$, let $x^\star$ be a minimizer of $f$, let $0<s\le 1/(3L)$, and let $(x_k,y_k)$ be a run of NAG-C with step size $s$ and Lyapunov function $\mathcal E$ of (4.6). Then for every $k\ge2$
--   $$
--   f(x_k)-f(x^\star)\le\frac{\mathcal E(k)}{s(k+3)(k+1)}\le\frac{\mathcal E(2)}{s(k+3)(k+1)}\le\frac{119\,\|x_0-x^\star\|^2}{s(k+1)^2}.
--   $$
--
--   This is the function-value rate of Theorem 6 for $k\ge2$.
--
--   **Formalization Note** Each of the three inequalities of the chain is a separate conjunct. The minimizer $x^\star$ is a hypothesis.
-- source:
--   Shi, Du, Jordan & Su, Understanding the Acceleration Phenomenon via High-Resolution Differential Equations, arXiv:1810.08907v3, p. 27, (4.12), proof of Theorem 6

import Mathlib
import Definitions.Def_HighResODE_NAGC_Setting

namespace HighResODE.NAGC

open scoped InnerProductSpace

/-- (4.12), proof of Theorem 6, p. 27: the three links of the chain, for `k ≥ 2`. -/
theorem eq_4_12 {n : ℕ} (f : HighResODE.NAGSC.E n → ℝ) (L s : ℝ) (hf : HighResODE.NAGSC.IsF1 f L) (xs : HighResODE.NAGSC.E n)
    (hmin : ∀ z : HighResODE.NAGSC.E n, f xs ≤ f z) (hs : 0 < s) (hsL : s ≤ 1 / (3 * L))
    (x y : ℕ → HighResODE.NAGSC.E n) (hrun : IsNAGC f s x y) (k : ℕ) (hk : 2 ≤ k) :
    f (x k) - f xs ≤ lyap f s xs x k / (s * ((k : ℝ) + 3) * ((k : ℝ) + 1)) ∧
    lyap f s xs x k / (s * ((k : ℝ) + 3) * ((k : ℝ) + 1))
        ≤ lyap f s xs x 2 / (s * ((k : ℝ) + 3) * ((k : ℝ) + 1)) ∧
    lyap f s xs x 2 / (s * ((k : ℝ) + 3) * ((k : ℝ) + 1))
        ≤ 119 * ‖x 0 - xs‖ ^ 2 / (s * ((k : ℝ) + 1) ^ 2) := by sorry

end HighResODE.NAGC
