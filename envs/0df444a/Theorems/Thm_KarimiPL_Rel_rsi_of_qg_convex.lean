-- Prove2me | Theorems.Thm_KarimiPL_Rel_rsi_of_qg_convex
-- name    : KarimiPL.Rel.rsi_of_qg_convex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:44:33.751601+00:00
-- url     : https://prove2.me/theorems/5aff49f4-74f4-497c-9214-1ea0cf8dd611
-- title:
--   Appendix A, p. 12 — for convex f, QG with constant μ implies RSI with constant μ/2
-- statement:
--   Let $f:\mathbb R^d\to\mathbb R$ be differentiable and convex. Let $x^*$ be a global minimizer, $f^*=f(x^*)$, let $\mathcal X^*$ be the set of global minimizers and let $x\mapsto x_p$ be a projection onto $\mathcal X^*$. Let $\mu>0$. If $f$ has quadratic growth, $f(x)-f^*\ge\frac\mu2\|x_p-x\|^2$ for all $x$, then $f$ satisfies the restricted secant inequality with constant $\mu/2$: for every $x$,
--   $$\langle\nabla f(x),x-x_p\rangle\ge\frac\mu2\|x_p-x\|^2.$$
--
--   This closes the cycle RSI → EB → PL → QG → RSI for convex functions, which gives the second line of Theorem 2.
--
--   **Formalization Note** Convexity is `ConvexOn ℝ Set.univ f`. The paper's standing Lipschitz-gradient assumption is not used by this step and is omitted.
-- source:
--   Karimi, Nutini, Schmidt, arXiv:1608.04636v4, Appendix A, bullet "QG + Convex → RSI", p. 12

import Mathlib
import Definitions.Def_ShiOptrates_FunctionClass
import Definitions.Def_KarimiPL_Rel_Conditions

namespace KarimiPL.Rel

theorem rsi_of_qg_convex {d : ℕ} (f : E d → ℝ) (hdiff : Differentiable ℝ f)
    (hconv : ConvexOn ℝ Set.univ f)
    (xstar : E d) (hxstar : ∀ y, f xstar ≤ f y)
    (p : E d → E d) (hp : IsProjSel f p)
    (μ : ℝ) (hμ : 0 < μ) (hQG : QG f p (f xstar) μ) :
    RSI f p (μ / 2) := by sorry

end KarimiPL.Rel
