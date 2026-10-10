-- Prove2me | Theorems.Thm_NecoaraNG_Compose_eq_39
-- name    : NecoaraNG.Compose.eq_39
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:42:57.627804+00:00
-- url     : https://prove2.me/theorems/6ad6da4e-012d-40ec-b63a-fae6998a6632
-- title:
--   (39), p. 14 — Ax* and ∇f(x*) are constant over the optimal set of (38)
-- statement:
--   Consider problem (38), $\min\{f(x)=g(Ax): Cx\le d\}$, with $g:\mathbb R^m\to\mathbb R$ differentiable and $\sigma_g$-strongly convex ($\sigma_g>0$) with $L_g$-Lipschitz gradient, $A\ne0$, and a nonempty optimal set $X^*$. Then there is a unique pair $(t^*,T^*)\in\mathbb R^m\times\mathbb R^n$ with
--   $$Ax^*=t^*,\qquad\nabla f(x^*)=T^*\qquad\forall x^*\in X^*.$$
--   Equivalently: for all $x_1^*,x_2^*\in X^*$, $Ax_1^*=Ax_2^*$ and $\nabla f(x_1^*)=\nabla f(x_2^*)$.
--
--   This is the step that makes the optimal set polyhedral, and so makes Hoffman's inequality applicable.
--
--   **Formalization Note** The existence of a unique pair is stated as constancy of both maps on $X^*$, which is the same statement once $X^*$ is nonempty (a named optimal point $x^*$ is a hypothesis). Lipschitz continuity of $\nabla g$ is kept as on the page, although the conclusion does not need it.
-- source:
--   Necoara, Nesterov & Glineur, Linear convergence of first order methods for non-strongly convex optimization, arXiv:1504.06298v4, p. 14, (39)

import Mathlib
import Definitions.Def_NecoaraNG_Compose_Setting

open scoped InnerProductSpace

namespace NecoaraNG.Compose

theorem eq_39 {n m p : ℕ} (A : NecoaraNG.Chain.E n →L[ℝ] NecoaraNG.Chain.E m) (hA : A ≠ 0) (C : NecoaraNG.Chain.E n →L[ℝ] NecoaraNG.Chain.E p) (d : NecoaraNG.Chain.E p)
    (g : NecoaraNG.Chain.E m → ℝ) (hgdiff : ∀ u, DifferentiableAt ℝ g u) (σg Lg : ℝ) (hσg : 0 < σg)
    (hg : StrongConvexOn Set.univ σg g)
    (hLg : ∀ u v, ‖gradient g u - gradient g v‖ ≤ Lg * ‖u - v‖)
    (xstar : NecoaraNG.Chain.E n) (hxstar : xstar ∈ NecoaraNG.Chain.optSet (polyhedron C d) (fun x => g (A x))) :
    ∀ x1 ∈ NecoaraNG.Chain.optSet (polyhedron C d) (fun x => g (A x)),
      ∀ x2 ∈ NecoaraNG.Chain.optSet (polyhedron C d) (fun x => g (A x)),
        A x1 = A x2 ∧
          gradient (fun z => g (A z)) x1 = gradient (fun z => g (A z)) x2 := by sorry

end NecoaraNG.Compose
