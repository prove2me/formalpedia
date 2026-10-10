-- Prove2me | Theorems.Thm_HighResODE_NAGC_eq_4_10
-- name    : HighResODE.NAGC.eq_4_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:25:54.344758+00:00
-- url     : https://prove2.me/theorems/77f2fe6a-efed-4913-9e99-f83fb94c383d
-- title:
--   (4.10), p. 26 — min_{4≤i≤k}‖∇f(xᵢ)‖² ≤ 72(E(3) − E(k))/(s²(k + 1)³) ≤ 72E(3)/(s²(k + 1)³)
-- statement:
--   Let $f\in\mathcal F^1_L(\mathbb R^n)$, let $x^\star$ be a minimizer of $f$, let $0<s\le 1/(3L)$, and let $(x_k,y_k)$ be a run of NAG-C with step size $s$ and Lyapunov function $\mathcal E$ of (4.6). Then for every $k\ge4$
--   $$
--   \min_{4\le i\le k}\|\nabla f(x_i)\|^2\le\frac{72\bigl(\mathcal E(3)-\mathcal E(k)\bigr)}{s^2(k+1)^3}\le\frac{72\,\mathcal E(3)}{s^2(k+1)^3}.
--   $$
--
--   This reduces the gradient-norm rate for $k\ge4$ to a bound on the single number $\mathcal E(3)$.
--
--   **Formalization Note** The minimum is a finite minimum over $\{4,\dots,k\}$ (`Finset.inf'` on `Finset.Icc 4 k`, nonempty because $k\ge4$). The minimizer $x^\star$ is a hypothesis.
-- source:
--   Shi, Du, Jordan & Su, Understanding the Acceleration Phenomenon via High-Resolution Differential Equations, arXiv:1810.08907v3, p. 26, (4.10), proof of Theorem 6

import Mathlib
import Definitions.Def_HighResODE_NAGC_Setting

namespace HighResODE.NAGC

open scoped InnerProductSpace

/-- (4.10), proof of Theorem 6, p. 26. -/
theorem eq_4_10 {n : ℕ} (f : HighResODE.NAGSC.E n → ℝ) (L s : ℝ) (hf : HighResODE.NAGSC.IsF1 f L) (xs : HighResODE.NAGSC.E n)
    (hmin : ∀ z : HighResODE.NAGSC.E n, f xs ≤ f z) (hs : 0 < s) (hsL : s ≤ 1 / (3 * L))
    (x y : ℕ → HighResODE.NAGSC.E n) (hrun : IsNAGC f s x y) (k : ℕ) (hk : 4 ≤ k) :
    (Finset.Icc 4 k).inf' (Finset.nonempty_Icc.mpr hk) (fun i => ‖gradient f (x i)‖ ^ 2)
        ≤ 72 * (lyap f s xs x 3 - lyap f s xs x k) / (s ^ 2 * ((k : ℝ) + 1) ^ 3) ∧
    72 * (lyap f s xs x 3 - lyap f s xs x k) / (s ^ 2 * ((k : ℝ) + 1) ^ 3)
        ≤ 72 * lyap f s xs x 3 / (s ^ 2 * ((k : ℝ) + 1) ^ 3) := by sorry

end HighResODE.NAGC
