-- Prove2me | Theorems.Thm_NecoaraNG_Compose_lipschitz_grad
-- name    : NecoaraNG.Compose.lipschitz_grad
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:43:16.049106+00:00
-- url     : https://prove2.me/theorems/4fb508c5-b176-453a-aa64-ffe615a7e0f5
-- title:
--   Proof of Theorem 8, p. 14 — f(x) = g(Ax) has Lipschitz gradient with L_f = L_g‖A‖²
-- statement:
--   Let $A:\mathbb R^n\to\mathbb R^m$ be linear, $X=\{x: Cx\le d\}$ a polyhedron, and $g:\mathbb R^m\to\mathbb R$ differentiable with $L_g$-Lipschitz gradient on $\mathbb R^m$. Then $f(x)=g(Ax)$ has Lipschitz continuous gradient on $X$ with constant $L_f=L_g\|A\|^2$:
--   $$\|\nabla f(x)-\nabla f(y)\|\le L_g\|A\|^2\,\|x-y\|\qquad\forall x,y\in X.$$
--
--   This is the first half of Theorem 8: the smoothness constant of the composition.
--
--   **Formalization Note** $\|A\|$ is the operator norm (the spectral norm). Strong convexity of $g$, $A\neq0$ and the optimal point are not needed for this part and are dropped. The page's "$L_g$-Lipschitz continuous gradient on $X$" is read on $\mathbb R^m$, the domain of $g$.
-- source:
--   Necoara, Nesterov & Glineur, Linear convergence of first order methods for non-strongly convex optimization, arXiv:1504.06298v4, p. 14, proof of Theorem 8, first display

import Mathlib
import Definitions.Def_NecoaraNG_Compose_Setting

open scoped InnerProductSpace

namespace NecoaraNG.Compose

theorem lipschitz_grad {n m p : ℕ} (A : NecoaraNG.Chain.E n →L[ℝ] NecoaraNG.Chain.E m) (C : NecoaraNG.Chain.E n →L[ℝ] NecoaraNG.Chain.E p) (d : NecoaraNG.Chain.E p)
    (g : NecoaraNG.Chain.E m → ℝ) (hgdiff : ∀ u, DifferentiableAt ℝ g u) (Lg : ℝ)
    (hLg : ∀ u v, ‖gradient g u - gradient g v‖ ≤ Lg * ‖u - v‖) :
    LipGradOn (polyhedron C d) (fun x => g (A x)) (Lg * ‖A‖ ^ 2) := by sorry

end NecoaraNG.Compose
