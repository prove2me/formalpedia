-- Prove2me | Theorems.Thm_NAGFlow_APGM_eq_112
-- name    : NAGFlow.APGM.eq_112
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:31:25.789386+00:00
-- url     : https://prove2.me/theorems/6c550527-ba0f-4f9e-a7cf-2089875af3d1
-- title:
--   (112), p. 29 — (z − prox_{ηg}(z))/η ∈ ∂g(prox_{ηg}(z))
-- statement:
--   Let $V$ be a real Hilbert space, $g:V\to\mathbb R\cup\{+\infty\}$ proper, closed and convex, and $\eta>0$. For every $z\in V$, if $p=\operatorname{prox}_{\eta g}(z)$, that is, $p$ minimises $g(y)+\frac1{2\eta}\|y-z\|^2$ over $y\in V$, then
--   $$\frac{z-p}{\eta}\in\partial g(p),$$
--   where $\partial g$ is the subdifferential (105): $q\in\partial g(p)$ iff $g(y)\ge g(p)+\langle q,y-p\rangle$ for all $y$.
--
--   This is the optimality condition of the proximal subproblem; it is what turns the proximal-gradient step into a gradient-like step in §7.2.
--
--   **Formalization Note.** $g$ is encoded by its domain $D$ and its real values on $D$; $p\in D$ is part of the prox predicate, and the subgradient inequality is required for $y\in D$ (it is automatic for $y\notin D$, where $g=+\infty$).
-- source:
--   Luo & Chen, arXiv:1909.03145v4, §7.2.1, (112), p. 29; (8), p. 2; (105), p. 26

import Mathlib
import Definitions.Def_NAGFlow_APGM_Setting

namespace NAGFlow.APGM

/-- The proximal optimality condition (112) (Luo & Chen, arXiv:1909.03145v4, §7.2.1, p. 29). Let
`g : V → ℝ ∪ {+∞}` be proper, closed and convex (encoded by `(g, D)`, `D = dom g`), `η > 0` and
`z ∈ V`. If `p = prox_{ηg}(z)`, then `(z − p)/η ∈ ∂g(p)`. -/
theorem eq_112 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (g : V → ℝ) (D : Set V) (hg : IsProperClosedConvex g D) (η : ℝ) (hη : 0 < η)
    (z p : V) (hp : IsProx g D η z p) :
    (1 / η) • (z - p) ∈ subdiff g D p := by sorry

end NAGFlow.APGM
