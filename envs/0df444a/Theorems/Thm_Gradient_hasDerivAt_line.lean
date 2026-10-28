-- Prove2me | Theorems.Thm_Gradient_hasDerivAt_line
-- name    : Gradient.hasDerivAt_line
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T00:30:35.688188+00:00
-- url     : https://prove2.me/theorems/f5efcd29-935b-4e29-852a-710dcc1be3b7
-- title:
--   Derivative of a differentiable function along a line
-- statement:
--   Let $H$ be a real inner product space and let $F : H \to \mathbb{R}$ have gradient
--   $\nabla F(x)$ at every point. Fix $x, w \in H$ and consider the restriction of $F$ to the line
--   through $x$ in direction $w$, namely $\phi(s) = F(x + s w)$ for $s \in \mathbb{R}$. Then $\phi$
--   is differentiable at every $t \in \mathbb{R}$, with
--
--   $$
--   \phi'(t) \;=\; \bigl\langle \nabla F(x + t w),\, w \bigr\rangle .
--   $$
--
--   This is the chain rule in the one case that matters for optimization: it turns a statement about
--   a function on a space into a statement about a function of one real variable, so that the mean
--   value theorem and one-dimensional integration become available. It is the standard bridge used
--   to derive the descent lemma and the cocoercivity inequality from a bound on the gradient.
-- source:
--   Y. Nesterov, Lectures on Convex Optimization, 2nd ed., Springer 2018, §2.1.1; carved from the accepted proof of RelaxedPRS.Linear.theorem_4_3, https://prove2.me/submissions/23766413-5769-4c79-8267-9febba86ff5e

import Mathlib

set_option autoImplicit false
open scoped InnerProductSpace
open scoped RealInnerProductSpace

theorem Gradient.hasDerivAt_line {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {F : E → ℝ} {G : E → E} (hF : ∀ x, HasGradientAt F (G x) x)
    (x w : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => F (x + s • w)) ⟪G (x + t • w), w⟫ t := by sorry
