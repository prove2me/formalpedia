-- Prove2me | Theorems.Thm_KarimiPL_GD_quadUpper_of_lipschitz
-- name    : KarimiPL.GD.quadUpper_of_lipschitz
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-08T23:56:04.339161+00:00
-- url     : https://prove2.me/theorems/22b67373-e6cb-4cf4-a5eb-9019f5abb7ac
-- title:
--   §2, equation (2) — an L-Lipschitz gradient gives the quadratic upper bound
-- statement:
--   Let $f:\mathbb R^d\to\mathbb R$ be differentiable and let its gradient be $L$-Lipschitz: $\|\nabla f(x)-\nabla f(y)\|\le L\|x-y\|$ for all $x,y$. Then, for all $x,y\in\mathbb R^d$,
--
--   $$
--   f(y)\le f(x)+\langle\nabla f(x),y-x\rangle+\frac L2\|y-x\|^2.
--   $$
--
--   This is the smoothness inequality (2) used in the rate proof. It relates the paper's Lipschitz-gradient assumption to the quadratic upper-bound predicate reused by the one-step results.
--
--   **Formalization Note** The statement does not require $L>0$: the implication from a Lipschitz bound to the displayed inequality also covers the degenerate point space $d=0$. The main theorem assumes $L>0$ because its step size divides by $L$.
-- source:
--   Karimi, Nutini, Schmidt, arXiv:1608.04636v4, §2, equation (2) and preceding sentence, p. 2

import Mathlib
import Definitions.Def_ShiOptrates_FunctionClass
open scoped InnerProductSpace

namespace KarimiPL.GD

theorem quadUpper_of_lipschitz {d : ℕ}
    (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (hdiff : Differentiable ℝ f)
    (L : ℝ) (hLip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) :
    ShiOptRates.QuadUpper f (gradient f) L := by sorry

end KarimiPL.GD
