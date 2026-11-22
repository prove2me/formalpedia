-- Prove2me | Theorems.Thm_KarimiPL_Rel_pl_of_eb
-- name    : KarimiPL.Rel.pl_of_eb
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:42:21.290974+00:00
-- url     : https://prove2.me/theorems/75897e7d-bbc5-462d-9fc1-d361d99f33c4
-- title:
--   Appendix A, p. 12 — under an L-Lipschitz gradient, EB with constant μ implies PL with constant μ²/L
-- statement:
--   Let $f:\mathbb R^d\to\mathbb R$ be differentiable with an $L$-Lipschitz gradient, $\|\nabla f(x)-\nabla f(y)\|\le L\|x-y\|$, where $L>0$. Let $x^*$ be a global minimizer, $f^*=f(x^*)$, let $\mathcal X^*$ be the set of global minimizers and let $x\mapsto x_p$ be a projection onto $\mathcal X^*$. Let $\mu>0$. If $f$ satisfies the error bound $\|\nabla f(x)\|\ge\mu\|x_p-x\|$ for all $x$, then $f$ satisfies the Polyak–Łojasiewicz inequality with constant $\mu^2/L$: for every $x$,
--   $$\frac12\|\nabla f(x)\|^2\ge\frac{\mu^2}{L}\bigl(f(x)-f^*\bigr).$$
--
--   Together with the converse (PL implies EB) this gives the equivalence EB ≡ PL of Theorem 2.
--
--   **Formalization Note** The paper's text concludes "the PL inequality with constant µ/L", but its displayed bound $(L/2\mu)\|\nabla f(x)\|^2$ should read $(L/(2\mu^2))\|\nabla f(x)\|^2$, since EB gives $\|x_p-x\|^2\le\|\nabla f(x)\|^2/\mu^2$; the constant that the argument yields is $\mu^2/L$, which is what is stated here. The PL inequality is the published predicate `ShiOptRates.PolyakLojasiewicz f (gradient f) c (f x*)`, i.e. $2c(f(x)-f(x^*))\le\|\nabla f(x)\|^2$, the paper's (3) multiplied by 2.
-- source:
--   Karimi, Nutini, Schmidt, arXiv:1608.04636v4, Appendix A, bullet "EB → PL", p. 12 (constant corrected from the printed µ/L to µ²/L)

import Mathlib
import Definitions.Def_ShiOptrates_FunctionClass
import Definitions.Def_KarimiPL_Rel_Conditions

namespace KarimiPL.Rel

theorem pl_of_eb {d : ℕ} (f : E d → ℝ) (hdiff : Differentiable ℝ f)
    (L : ℝ) (hL : 0 < L) (hLip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (xstar : E d) (hxstar : ∀ y, f xstar ≤ f y)
    (p : E d → E d) (hp : IsProjSel f p)
    (μ : ℝ) (hμ : 0 < μ) (hEB : EB f p μ) :
    ShiOptRates.PolyakLojasiewicz f (gradient f) (μ ^ 2 / L) (f xstar) := by sorry

end KarimiPL.Rel
