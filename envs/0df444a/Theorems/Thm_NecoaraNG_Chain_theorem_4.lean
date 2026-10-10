-- Prove2me | Theorems.Thm_NecoaraNG_Chain_theorem_4
-- name    : NecoaraNG.Chain.theorem_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-09T11:50:13.306738+00:00
-- url     : https://prove2.me/theorems/731f6acb-d934-4c45-8a4e-bb66d133a532
-- title:
--   Theorem 4, p. 9 — (7) ⇒ (10) ⇒ (17) ⇒ (13) ⇒ (22) with one constant κ, i.e. S ⊆ qS ⊆ G ⊆ U ⊆ F
-- statement:
--   Let $X\subseteq\mathbb R^n$ be a closed convex set and $f$ a convex function on $X$, differentiable at every point of $X$, whose gradient is Lipschitz on $X$ with constant $L_f>0$:
--   $$\|\nabla f(x)-\nabla f(y)\|\le L_f\|x-y\|\qquad\forall x,y\in X.$$
--   Assume the optimal set $X^*=\arg\min_{x\in X}f(x)$ is nonempty, write $f^*$ for the optimal value and $\bar x=[x]_{X^*}$ for the projection of $x$ onto $X^*$. Fix $\kappa>0$ and consider the five conditions (for all $x,y\in X$):
--
--   1. (7): $f(y)\ge f(x)+\langle\nabla f(x),y-x\rangle+\frac{\kappa}{2}\|x-y\|^2$;
--   2. (10): $f^*\ge f(x)+\langle\nabla f(x),\bar x-x\rangle+\frac{\kappa}{2}\|x-\bar x\|^2$;
--   3. (17): $\langle\nabla f(x)-\nabla f(\bar x),x-\bar x\rangle\ge\kappa\|x-\bar x\|^2$;
--   4. (13): $f(x)\ge f^*+\langle\nabla f(\bar x),x-\bar x\rangle+\frac{\kappa}{2}\|x-\bar x\|^2$;
--   5. (22): $f(x)-f^*\ge\frac{\kappa}{2}\|x-\bar x\|^2$.
--
--   Then, with the same constant $\kappa$ throughout,
--   $$(7)\ \Rightarrow\ (10)\ \Rightarrow\ (17)\ \Rightarrow\ (13)\ \Rightarrow\ (22).$$
--   Equivalently, the function classes satisfy
--   $$\mathcal S_{L_f,\kappa}(X)\subseteq q\mathcal S_{L_f,\kappa}(X)\subseteq\mathcal G_{L_f,\kappa}(X)\subseteq\mathcal U_{L_f,\kappa}(X)\subseteq\mathcal F_{L_f,\kappa}(X).$$
--
--   This chain places quasi-strong convexity and the other relaxations between strong convexity and quadratic functional growth; the paper's linear-convergence results for gradient methods are stated for these weaker classes.
--
--   **Formalization Note** The theorem is a conjunction of the four implications under the standing assumptions (closed convex $X$, convex $f$ differentiable on $X$, (1) with $L_f>0$, a minimiser $x^*\in X^*$, $\kappa>0$); since every class bundles convexity and (1), this conjunction is exactly (23). $f^*$ is written $f(\bar x)$, and conditions 2–5 are required for every nearest point $\bar x$ of $X^*$ (unique here). "Continuously differentiable" in the paper's definitions is covered on $X$ by (1); differentiability is assumed at the points of $X$ in the ambient space.
-- source:
--   Necoara, Nesterov & Glineur, Linear convergence of first order methods for non-strongly convex optimization, arXiv:1504.06298v4, p. 9, Theorem 4, (23)

import Mathlib
import Definitions.Def_NecoaraNG_Chain_Setting

namespace NecoaraNG.Chain

open scoped InnerProductSpace

/-- Theorem 4, p. 9: the chain `(7) ⇒ (10) ⇒ (17) ⇒ (13) ⇒ (22)` with one constant `κ`, i.e. the
inclusions (23) `S ⊆ qS ⊆ G ⊆ U ⊆ F` of the classes with indices `L_f, κ`. -/
theorem theorem_4 {n : ℕ} (X : Set (E n)) (hXc : IsClosed X) (hXconv : Convex ℝ X)
    (f : E n → ℝ) (hf : ConvexOn ℝ X f) (hdiff : ∀ x ∈ X, DifferentiableAt ℝ f x)
    (Lf : ℝ) (hLf : 0 < Lf)
    (hL : ∀ x ∈ X, ∀ y ∈ X, ‖gradient f x - gradient f y‖ ≤ Lf * ‖x - y‖)
    (xstar : E n) (hxstar : xstar ∈ optSet X f) (κ : ℝ) (hκ : 0 < κ) :
    (StrongIneq X f κ → QuasiStrong X f κ) ∧
      (QuasiStrong X f κ → QuadGradGrowth X f κ) ∧
      (QuadGradGrowth X f κ → QuadUnder X f κ) ∧
      (QuadUnder X f κ → QuadFunGrowth X f κ) := by sorry

end NecoaraNG.Chain
