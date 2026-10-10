-- Prove2me | Theorems.Thm_HighResODE_NAGC_C_1_4
-- name    : HighResODE.NAGC.C_1_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:26:26.879756+00:00
-- url     : https://prove2.me/theorems/953c555e-9362-4381-b7e7-18f378032b89
-- title:
--   App. C.1.4, p. 61 — E(3) ≤ E(2) ≤ 119‖x₀ − x⋆‖²
-- statement:
--   Let $f\in\mathcal F^1_L(\mathbb R^n)$, let $x^\star$ be a minimizer of $f$, let $0<s\le 1/(3L)$, and let $(x_k,y_k)$ be a run of NAG-C with step size $s$ and Lyapunov function $\mathcal E$ of (4.6). Then
--   $$
--   \mathcal E(3)\le\mathcal E(2)\le119\,\|x_0-x^\star\|^2 .
--   $$
--
--   This is the initial-value bound that, inserted in (4.10) and (4.12), produces the explicit constants $8568=72\cdot119$ and $119$ of Theorem 6.
--
--   **Formalization Note** The minimizer $x^\star$ is a hypothesis.
-- source:
--   Shi, Du, Jordan & Su, Understanding the Acceleration Phenomenon via High-Resolution Differential Equations, arXiv:1810.08907v3, p. 61, App. C.1.4 (consequence of (C.9) and Lemma 4.3)

import Mathlib
import Definitions.Def_HighResODE_NAGC_Setting

namespace HighResODE.NAGC

open scoped InnerProductSpace

/-- App. C.1.4, p. 61: `E(3) ≤ E(2) ≤ 119‖x₀ − x⋆‖²`. -/
theorem C_1_4 {n : ℕ} (f : HighResODE.NAGSC.E n → ℝ) (L s : ℝ) (hf : HighResODE.NAGSC.IsF1 f L) (xs : HighResODE.NAGSC.E n)
    (hmin : ∀ z : HighResODE.NAGSC.E n, f xs ≤ f z) (hs : 0 < s) (hsL : s ≤ 1 / (3 * L))
    (x y : ℕ → HighResODE.NAGSC.E n) (hrun : IsNAGC f s x y) :
    lyap f s xs x 3 ≤ lyap f s xs x 2 ∧ lyap f s xs x 2 ≤ 119 * ‖x 0 - xs‖ ^ 2 := by sorry

end HighResODE.NAGC
