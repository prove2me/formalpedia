-- Prove2me | Theorems.Thm_HighResODE_NAGC_eq_4_11
-- name    : HighResODE.NAGC.eq_4_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:26:56.467934+00:00
-- url     : https://prove2.me/theorems/df4b6219-f6f0-46ac-ae20-c758d9c1bc9d
-- title:
--   (4.11), p. 26 — min_{4≤i≤k}‖∇f(xᵢ)‖² ≤ 8568‖x₀ − x⋆‖²/(s²(k + 1)³) for k ≥ 4
-- statement:
--   Let $f\in\mathcal F^1_L(\mathbb R^n)$, let $x^\star$ be a minimizer of $f$, let $0<s\le 1/(3L)$, and let $(x_k,y_k)$ be a run of NAG-C with step size $s$. Then for every $k\ge4$
--   $$
--   \min_{4\le i\le k}\|\nabla f(x_i)\|^2\le\frac{8568\,\|x_0-x^\star\|^2}{s^2(k+1)^3}.
--   $$
--
--   This is the gradient-norm rate of Theorem 6 restricted to the iterates with index at least $4$.
--
--   **Formalization Note** The minimum is `Finset.inf'` over `Finset.Icc 4 k`. The minimizer $x^\star$ is a hypothesis.
-- source:
--   Shi, Du, Jordan & Su, Understanding the Acceleration Phenomenon via High-Resolution Differential Equations, arXiv:1810.08907v3, p. 26, (4.11), proof of Theorem 6

import Mathlib
import Definitions.Def_HighResODE_NAGC_Setting

namespace HighResODE.NAGC

open scoped InnerProductSpace

/-- (4.11), proof of Theorem 6, p. 26. -/
theorem eq_4_11 {n : ℕ} (f : HighResODE.NAGSC.E n → ℝ) (L s : ℝ) (hf : HighResODE.NAGSC.IsF1 f L) (xs : HighResODE.NAGSC.E n)
    (hmin : ∀ z : HighResODE.NAGSC.E n, f xs ≤ f z) (hs : 0 < s) (hsL : s ≤ 1 / (3 * L))
    (x y : ℕ → HighResODE.NAGSC.E n) (hrun : IsNAGC f s x y) (k : ℕ) (hk : 4 ≤ k) :
    (Finset.Icc 4 k).inf' (Finset.nonempty_Icc.mpr hk) (fun i => ‖gradient f (x i)‖ ^ 2)
      ≤ 8568 * ‖x 0 - xs‖ ^ 2 / (s ^ 2 * ((k : ℝ) + 1) ^ 3) := by sorry

end HighResODE.NAGC
