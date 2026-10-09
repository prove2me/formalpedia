-- Prove2me | Theorems.Thm_ModernOnlineLearning_OMD_theorem_6_9
-- name    : ModernOnlineLearning.OMD.theorem_6_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:36:45.676257+00:00
-- url     : https://prove2.me/theorems/ce597f62-7f22-41d2-8ead-bde0778ffa9d
-- title:
--   Theorem 6.9, p. 66 — unique minimizer of a closed strongly convex function
-- statement:
--   Let $f$ be a proper, closed function on a finite-dimensional real normed space, with finite domain $D$. Suppose $f$ is $\lambda$-strongly convex on $D$ for $\lambda>0$, and its subdifferential is nonempty at some point of $D$. Then there is exactly one $x\in D$ such that
--
--   $$f(x)\le f(z)\qquad\text{for every }z\in D.$$
--
--   This existence and uniqueness result supplies the minimizer of each strongly convex mirror-descent update.
--
--   **Formalization Note** The extended-valued function is represented by a real-valued function on its exact finite domain $D$ and by $+\infty$ elsewhere. Closedness is closedness of that extended function's epigraph. The nonempty-subdifferential hypothesis is an explicit point and continuous linear subgradient on $D$.
-- source:
--   Orabona, arXiv:1912.13213v10, Theorem 6.9, p. 66

import Mathlib
import Definitions.Def_ModernOnlineLearning_OMD_Defs

namespace ModernOnlineLearning.OMD

/-- Orabona, Theorem 6.9, p. 66.  The extended function is represented by a
real-valued `f` on its exact finite domain `D`, and `+∞` elsewhere. -/
theorem theorem_6_9 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (D : Set E) (f : E → ℝ) (lam : ℝ)
    (hlam : 0 < lam) (hclosed : IsClosedOnDomain D f)
    (hstrong : StrongConvexOn D lam f)
    (hsub : ∃ y ∈ D, ∃ g : E →L[ℝ] ℝ, IsSubgradientOn D f y g) :
    ∃! x : E, x ∈ D ∧ ∀ z ∈ D, f x ≤ f z := by sorry

end ModernOnlineLearning.OMD
