-- Prove2me | Theorems.Thm_HighResODE_NAGCODE_lemma_4_1_deriv
-- name    : HighResODE.NAGCODE.lemma_4_1_deriv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:28:03.092214+00:00
-- url     : https://prove2.me/theorems/7923e2ab-06ac-4875-b773-122e57cd0654
-- title:
--   Proof of Lemma 4.1, p. 23 — dE/dt = (2t + √s/2)(f(X) − f(x⋆)) − (√s + 2t)⟨X − x⋆, ∇f(X)⟩ − √s t(t + √s/2)‖∇f(X)‖²
-- statement:
--   Let $f\in\mathcal F^2_L(\mathbb R^n)$, let $x^\star$ be a minimizer of $f$, let $s>0$ and $t_0=1.5\sqrt s$, and let $X$ solve the high-resolution ODE of NAG-C (1.12) from $x_0$. Then the Lyapunov function $\mathcal E$ of (4.1) is differentiable on $[t_0,\infty)$ (one-sidedly at $t_0$), with
--   $$\frac{d\mathcal E(t)}{dt}=\Big(2t+\frac{\sqrt s}{2}\Big)\big(f(X)-f(x^\star)\big)-\big(\sqrt s+2t\big)\langle X-x^\star,\nabla f(X)\rangle-\sqrt s\,t\Big(t+\frac{\sqrt s}{2}\Big)\|\nabla f(X)\|^2$$
--   for every $t\ge t_0$, where $X=X(t)$.
--
--   This exact identity is the first step of the proof of Lemma 4.1: the Hessian term of the ODE cancels the derivative of the gradient term $t\sqrt s\nabla f(X)$ inside the squared norm of (4.1).
-- source:
--   Shi, Du, Jordan & Su, Understanding the Acceleration Phenomenon via High-Resolution Differential Equations, arXiv:1810.08907v3, p. 23, proof of Lemma 4.1, first display

import Mathlib
import Definitions.Def_HighResODE_NAGCODE_Setting

namespace HighResODE.NAGCODE

open scoped InnerProductSpace

/-- Proof of Lemma 4.1, p. 23: along a solution of (1.12), the Lyapunov function (4.1) has
derivative `(2t + √s/2)(f(X) − f(x⋆)) − (√s + 2t)⟨X − x⋆, ∇f(X)⟩ − √s t(t + √s/2)‖∇f(X)‖²`
at every `t ≥ t₀`. -/
theorem lemma_4_1_deriv {n : ℕ} (f : HighResODE.NAGSC.E n → ℝ) (L s : ℝ) (hf : IsF2 f L) (xs : HighResODE.NAGSC.E n)
    (hmin : ∀ z : HighResODE.NAGSC.E n, f xs ≤ f z) (hs : 0 < s) (x0 : HighResODE.NAGSC.E n) (X V : ℝ → HighResODE.NAGSC.E n)
    (hsol : IsNAGCODE f s x0 X V) :
    ∀ t : ℝ, t0 s ≤ t →
      HasDerivWithinAt (lyap f s xs X V)
        ((2 * t + Real.sqrt s / 2) * (f (X t) - f xs)
          - (Real.sqrt s + 2 * t) * ⟪X t - xs, gradient f (X t)⟫_ℝ
          - Real.sqrt s * t * (t + Real.sqrt s / 2) * ‖gradient f (X t)‖ ^ 2)
        (Set.Ici (t0 s)) t := by sorry

end HighResODE.NAGCODE
