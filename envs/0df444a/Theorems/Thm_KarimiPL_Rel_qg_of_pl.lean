-- Prove2me | Theorems.Thm_KarimiPL_Rel_qg_of_pl
-- name    : KarimiPL.Rel.qg_of_pl
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:44:31.337787+00:00
-- url     : https://prove2.me/theorems/925b5567-e39b-4733-8f8e-13387c846cc1
-- title:
--   Appendix A, pp. 13–14 — under an L-Lipschitz gradient, PL with constant μ implies QG with constant μ
-- statement:
--   Let $f:\mathbb R^d\to\mathbb R$ be differentiable with an $L$-Lipschitz gradient ($L>0$). Let $x^*$ be a global minimizer, $f^*=f(x^*)$, let $\mathcal X^*$ be the set of global minimizers and let $x\mapsto x_p$ be a projection onto $\mathcal X^*$. Let $\mu>0$. If $f$ satisfies the Polyak–Łojasiewicz inequality $\frac12\|\nabla f(x)\|^2\ge\mu(f(x)-f^*)$ for all $x$, then $f$ has quadratic growth with the same constant: for every $x$,
--   $$f(x)-f^*\ge\frac\mu2\|x-x_p\|^2.$$
--
--   No convexity is assumed. This is the link PL → QG of Theorem 2, and it also yields PL → EB.
--
--   **Formalization Note** PL is the published predicate `ShiOptRates.PolyakLojasiewicz f (gradient f) μ (f x*)`, the paper's (3) multiplied by 2. Since $\|x-x_p\|=\operatorname{dist}(x,\mathcal X^*)$, the conclusion does not depend on which nearest point $p$ selects.
-- source:
--   Karimi, Nutini, Schmidt, arXiv:1608.04636v4, Appendix A, bullet "PL → QG", pp. 13–14

import Mathlib
import Definitions.Def_ShiOptrates_FunctionClass
import Definitions.Def_KarimiPL_Rel_Conditions

namespace KarimiPL.Rel

theorem qg_of_pl {d : ℕ} (f : E d → ℝ) (hdiff : Differentiable ℝ f)
    (L : ℝ) (hL : 0 < L) (hLip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (xstar : E d) (hxstar : ∀ y, f xstar ≤ f y)
    (p : E d → E d) (hp : IsProjSel f p)
    (μ : ℝ) (hμ : 0 < μ) (hPL : ShiOptRates.PolyakLojasiewicz f (gradient f) μ (f xstar)) :
    QG f p (f xstar) μ := by sorry

end KarimiPL.Rel
