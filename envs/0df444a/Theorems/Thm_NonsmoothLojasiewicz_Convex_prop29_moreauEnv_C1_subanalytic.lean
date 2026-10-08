-- Prove2me | Theorems.Thm_NonsmoothLojasiewicz_Convex_prop29_moreauEnv_C1_subanalytic
-- name    : NonsmoothLojasiewicz.Convex.prop29_moreauEnv_C1_subanalytic
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T19:11:33.298377+00:00
-- url     : https://prove2.me/theorems/bdf5447a-9cbf-405e-86b5-02031b608d81
-- title:
--   Proposition 2.9: the epigraphical sum of $f$ and $\tfrac12\|\cdot\|^2$ is $C^1$ and subanalytic
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ be lower semicontinuous, convex and subanalytic with $\inf_{\mathbb R^n} f\in\mathbb R$. Define $h$ as the epigraphical sum of $f$ and $\tfrac12\|\cdot\|^2$,
--   $$h(x)=\inf\Big\{f(u)+\tfrac12\|x-u\|^2:\ u\in\mathbb R^n\Big\},\qquad x\in\mathbb R^n.$$
--   Then $h$ is a real-valued function of class $C^1$, and $h$ is subanalytic.
--
--   Subanalyticity is not stable under infimal operations in general, because projections of unbounded subanalytic sets need not be subanalytic; the proposition shows that the Moreau regularization of a convex subanalytic function stays in the class. It is the first step of the proof of Theorem 3.3.
--
--   **Formalization Note** $h$ is the `EReal`-valued `moreauEnv f`; the conclusion provides a real-valued $C^1$ function equal to it everywhere. The hypothesis $\inf f\in\mathbb R$ is `GammaZero f` (which gives $f\not\equiv+\infty$, so $\inf f<+\infty$) together with $\inf f\neq-\infty$.
-- source:
--   Bolte, Daniilidis & Lewis, SIAM J. Optim. 17 (2007) 1205–1223, p. 1210, Proposition 2.9

import Mathlib
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_NonsmoothLojasiewicz_Continuous_IsSubanalytic
import Definitions.Def_NonsmoothLojasiewicz_Convex_moreauEnv

open Filter Topology
open MoreauProx.Characterization

namespace NonsmoothLojasiewicz.Convex

/-- Proposition 2.9 of Bolte–Daniilidis–Lewis (p. 1210): let `f : ℝⁿ → ℝ ∪ {+∞}` be lower
semicontinuous, convex and subanalytic with `inf f ∈ ℝ`. Then the epigraphical sum
`h(x) = inf {f(u) + ½‖x − u‖² : u ∈ ℝⁿ}` is real-valued, of class `C¹`, and subanalytic. -/
theorem prop29_moreauEnv_C1_subanalytic {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal)
    (hf : GammaZero f) (hsub : NonsmoothLojasiewicz.Continuous.IsSubanalyticFn f) (hinf : (⨅ y, f y) ≠ ⊥) :
    ∃ h : EuclideanSpace ℝ (Fin n) → ℝ,
      (∀ x, moreauEnv f x = (h x : EReal)) ∧ ContDiff ℝ 1 h ∧
        NonsmoothLojasiewicz.Continuous.IsSubanalyticFn (moreauEnv f) := by sorry

end NonsmoothLojasiewicz.Convex
