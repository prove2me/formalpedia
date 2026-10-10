-- Prove2me | Theorems.Thm_HighResODE_NAGC_eq_4_13
-- name    : HighResODE.NAGC.eq_4_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:26:08.621197+00:00
-- url     : https://prove2.me/theorems/4321594c-3018-4cc2-9594-a98083572a04
-- title:
--   (4.13), p. 27 — (k + 3)(vₖ + √s∇f(xₖ)) − k(vₖ₋₁ + √s∇f(xₖ₋₁)) = −k√s∇f(xₖ)
-- statement:
--   Let $s>0$, let $f:\mathbb R^n\to\mathbb R$, and let $(x_k,y_k)$ be a run of NAG-C with step size $s$ and velocity $v_k=(x_{k+1}-x_k)/\sqrt s$. Then for every $k\ge1$
--   $$
--   (k+3)\bigl(v_k+\sqrt s\nabla f(x_k)\bigr)-k\bigl(v_{k-1}+\sqrt s\nabla f(x_{k-1})\bigr)=-k\sqrt s\,\nabla f(x_k),
--   $$
--   and, for $k=0$, $v_0+\sqrt s\nabla f(x_0)=0$.
--
--   This identity is what makes the gradient-corrected momentum $v_k+\sqrt s\nabla f(x_k)$ collapse in the difference $\mathcal E(k+1)-\mathcal E(k)$ in the proof of Lemma 4.3.
--
--   **Formalization Note** The first identity is stated with $k+1$ in place of $k$ for every $k\ge0$. The paper writes (4.13) without a range; at its $k=0$ the term with $v_{-1}$ is multiplied by $0$ and the identity reads $3(v_0+\sqrt s\nabla f(x_0))=0$, which is the second conjunct. No convexity or smoothness of $f$ is needed.
-- source:
--   Shi, Du, Jordan & Su, Understanding the Acceleration Phenomenon via High-Resolution Differential Equations, arXiv:1810.08907v3, p. 27, (4.13), proof of Lemma 4.3

import Mathlib
import Definitions.Def_HighResODE_NAGC_Setting

namespace HighResODE.NAGC

open scoped InnerProductSpace

/-- (4.13), p. 27: for the page's `k ≥ 1` (here `k + 1`, `k ≥ 0`), and the page's `k = 0`
instance `3(v₀ + √s∇f(x₀)) = 0`, in which the `v₋₁` term carries the factor `0`. -/
theorem eq_4_13 {n : ℕ} (f : HighResODE.NAGSC.E n → ℝ) (s : ℝ) (hs : 0 < s) (x y : ℕ → HighResODE.NAGSC.E n) (hrun : IsNAGC f s x y) :
    (∀ k : ℕ, ((k : ℝ) + 4) • (HighResODE.NAGSC.vel s x (k + 1) + Real.sqrt s • gradient f (x (k + 1)))
        - ((k : ℝ) + 1) • (HighResODE.NAGSC.vel s x k + Real.sqrt s • gradient f (x k))
        = -(((k : ℝ) + 1) * Real.sqrt s) • gradient f (x (k + 1))) ∧
    HighResODE.NAGSC.vel s x 0 + Real.sqrt s • gradient f (x 0) = 0 := by sorry

end HighResODE.NAGC
