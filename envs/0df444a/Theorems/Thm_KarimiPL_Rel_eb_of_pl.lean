-- Prove2me | Theorems.Thm_KarimiPL_Rel_eb_of_pl
-- name    : KarimiPL.Rel.eb_of_pl
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:44:27.503386+00:00
-- url     : https://prove2.me/theorems/662543c5-84b3-4d28-bc33-5838b2c9b130
-- title:
--   Appendix A, p. 12 — under an L-Lipschitz gradient, PL with constant μ implies EB with constant μ
-- statement:
--   Let $f:\mathbb R^d\to\mathbb R$ be differentiable with an $L$-Lipschitz gradient ($L>0$). Let $x^*$ be a global minimizer, $f^*=f(x^*)$, let $\mathcal X^*$ be the set of global minimizers and let $x\mapsto x_p$ be a projection onto $\mathcal X^*$. Let $\mu>0$. If $f$ satisfies the Polyak–Łojasiewicz inequality $\frac12\|\nabla f(x)\|^2\ge\mu(f(x)-f^*)$ for all $x$, then $f$ satisfies the error bound with the same constant: for every $x$,
--   $$\|\nabla f(x)\|\ge\mu\|x_p-x\|.$$
--
--   Together with EB → PL this gives the equivalence EB ≡ PL of Theorem 2.
--
--   **Formalization Note** PL is the published predicate `ShiOptRates.PolyakLojasiewicz f (gradient f) μ (f x*)`, the paper's (3) multiplied by 2.
-- source:
--   Karimi, Nutini, Schmidt, arXiv:1608.04636v4, Appendix A, bullet "PL → EB", p. 12

import Mathlib
import Definitions.Def_ShiOptrates_FunctionClass
import Definitions.Def_KarimiPL_Rel_Conditions

namespace KarimiPL.Rel

theorem eb_of_pl {d : ℕ} (f : E d → ℝ) (hdiff : Differentiable ℝ f)
    (L : ℝ) (hL : 0 < L) (hLip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (xstar : E d) (hxstar : ∀ y, f xstar ≤ f y)
    (p : E d → E d) (hp : IsProjSel f p)
    (μ : ℝ) (hμ : 0 < μ) (hPL : ShiOptRates.PolyakLojasiewicz f (gradient f) μ (f xstar)) :
    EB f p μ := by sorry

end KarimiPL.Rel
