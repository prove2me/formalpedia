-- Prove2me | Theorems.Thm_NecoaraNG_Chain_inclusion_11
-- name    : NecoaraNG.Chain.inclusion_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T11:46:53.983512+00:00
-- url     : https://prove2.me/theorems/57bc296c-6c08-41d1-b04f-b65fc3d2c534
-- title:
--   (11), p. 5 — the first inequality of (7) with constant κ implies quasi-strong convexity (10) with constant κ
-- statement:
--   Let $X\subseteq\mathbb R^n$ be closed and convex, let $f$ be convex on $X$, differentiable at every point of $X$, with $L_f$-Lipschitz gradient on $X$ ($L_f>0$), and assume the optimal set $X^*=\arg\min_{x\in X}f(x)$ is nonempty. Let $\kappa>0$. If
--   $$f(y)\ge f(x)+\langle\nabla f(x),y-x\rangle+\frac{\kappa}{2}\|x-y\|^2\qquad\forall x,y\in X,$$
--   then for every $x\in X$ and $\bar x=[x]_{X^*}$,
--   $$f^*\ge f(x)+\langle\nabla f(x),\bar x-x\rangle+\frac{\kappa}{2}\|x-\bar x\|^2 .$$
--
--   In class notation this is the inclusion $\mathcal S_{L_f,\kappa}(X)\subseteq q\mathcal S_{L_f,\kappa}(X)$, the first link of the chain (23).
--
--   **Formalization Note** $f^*$ is written $f(\bar x)$. The standing assumptions of the paper are kept as hypotheses for uniformity with the other links of the chain, although the implication itself only uses that $\bar x\in X^*\subseteq X$.
-- source:
--   Necoara, Nesterov & Glineur, Linear convergence of first order methods for non-strongly convex optimization, arXiv:1504.06298v4, p. 5, inclusion (11)

import Mathlib
import Definitions.Def_NecoaraNG_Chain_Setting

namespace NecoaraNG.Chain

open scoped InnerProductSpace

/-- (11), p. 5: the first inequality of (7) with constant `κ` implies (10) with constant `κ`. -/
theorem inclusion_11 {n : ℕ} (X : Set (E n)) (hXc : IsClosed X) (hXconv : Convex ℝ X)
    (f : E n → ℝ) (hf : ConvexOn ℝ X f) (hdiff : ∀ x ∈ X, DifferentiableAt ℝ f x)
    (Lf : ℝ) (hLf : 0 < Lf)
    (hL : ∀ x ∈ X, ∀ y ∈ X, ‖gradient f x - gradient f y‖ ≤ Lf * ‖x - y‖)
    (xstar : E n) (hxstar : xstar ∈ optSet X f) (κ : ℝ) (hκ : 0 < κ) :
    StrongIneq X f κ → QuasiStrong X f κ := by sorry

end NecoaraNG.Chain
