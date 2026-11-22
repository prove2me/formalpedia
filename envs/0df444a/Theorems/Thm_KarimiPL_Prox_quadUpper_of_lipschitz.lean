-- Prove2me | Theorems.Thm_KarimiPL_Prox_quadUpper_of_lipschitz
-- name    : KarimiPL.Prox.quadUpper_of_lipschitz
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-08T23:55:47.476481+00:00
-- url     : https://prove2.me/theorems/75f22bbb-771b-4cf7-be73-af23069b0882
-- title:
--   §2, (2), p. 2 — an $L$-Lipschitz gradient gives $f(y) \le f(x) + \langle \nabla f(x), y - x\rangle + \frac L2\|y - x\|^2$
-- statement:
--   Let $f : \mathbb R^d \to \mathbb R$ be differentiable with an $L$-Lipschitz continuous gradient,
--   $$
--   \|\nabla f(x) - \nabla f(y)\| \le L\,\|x - y\| \qquad \text{for all } x, y \in \mathbb R^d.
--   $$
--   Then for all $x, y \in \mathbb R^d$,
--   $$
--   f(y) \le f(x) + \langle \nabla f(x), y - x\rangle + \frac L2\,\|y - x\|^2. \tag{2}
--   $$
--
--   This is the quadratic upper bound (2) that the paper derives from its standing assumption of an $L$-Lipschitz gradient, and the only place the Lipschitz assumption enters the proof of Theorem 5.
--
--   **Formalization Note** The conclusion is the published predicate `ShiOptRates.QuadUpper f (gradient f) L`. The same statement is a milestone of mission I of this series; drafts cannot import drafts, so it is restated here.
-- source:
--   Karimi, Nutini, Schmidt, arXiv:1608.04636v4, §2, (2), p. 2

import Mathlib
import Definitions.Def_ShiOptrates_FunctionClass
import Definitions.Def_KarimiPL_Prox_Setting

open InnerProductSpace

namespace KarimiPL.Prox

theorem quadUpper_of_lipschitz {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (hdiff : Differentiable ℝ f) (L : ℝ)
    (hLip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) :
    ShiOptRates.QuadUpper f (gradient f) L := by sorry

end KarimiPL.Prox
