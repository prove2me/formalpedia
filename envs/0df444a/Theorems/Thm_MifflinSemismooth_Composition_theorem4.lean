-- Prove2me | Theorems.Thm_MifflinSemismooth_Composition_theorem4
-- name    : MifflinSemismooth.Composition.theorem4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:48:23.167235+00:00
-- url     : https://prove2.me/theorems/a6d5cf2f-9098-4940-a6b5-49c1786a5c95
-- title:
--   Theorem 4 — chain rule inclusion for generalized gradients
-- statement:
--   Let each $f_i:\mathbb R^n\to\mathbb R$ and $E:\mathbb R^m\to\mathbb R$ be Lipschitz on every bounded set. Put $Y(x)=(f_1(x),\ldots,f_m(x))$, $F=E\circ Y$, and let $G(x)$ be the convex hull of all $\sum_i w_i g^i$ with $g^i\in\partial f_i(x)$ and $w\in\partial E(Y(x))$. Then $F$ is also Lipschitz on every bounded set, and
--
--   $$\partial F(x)\subseteq G(x)\qquad\text{for every }x\in\mathbb R^n. $$
--
--   The result bounds the generalized gradient of a composition by component generalized gradients.
--
--   **Formalization Note** The paper defines local Lipschitzness by Lipschitzness on every bounded set. The inclusion uses its support-set definition of $\partial$, which Proposition 1(c) identifies with Clarke's gradient-limit construction.
-- source:
--   Mifflin, Semismooth and semiconvex functions in constrained optimization, IIASA Research Report RR-76-21 (December 1976), p. 12, Theorem 4, (4.1)

import Mathlib
import Definitions.Def_MifflinSemismooth_Composition_Setting
import Definitions.Def_ClarkeGradients_Shared_LipschitzOnBounded

namespace MifflinSemismooth.Composition

theorem theorem4 {n m : ℕ}
    (f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (E : EuclideanSpace ℝ (Fin m) → ℝ)
    (hf : ∀ i, ClarkeGradients.Shared.LipschitzOnBounded (f i))
    (hE : ClarkeGradients.Shared.LipschitzOnBounded E) :
    ClarkeGradients.Shared.LipschitzOnBounded (compF E f) ∧
      ∀ x, MifflinSemismooth.Extremal.genGrad (compF E f) x ⊆ G E f x := by sorry

end MifflinSemismooth.Composition
