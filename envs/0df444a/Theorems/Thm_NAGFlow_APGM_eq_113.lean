-- Prove2me | Theorems.Thm_NAGFlow_APGM_eq_113
-- name    : NAGFlow.APGM.eq_113
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:31:22.404751+00:00
-- url     : https://prove2.me/theorems/569e1d5a-7d69-4cc9-9649-3f7b2520f231
-- title:
--   (113), p. 29 — G_f(x, η) − ∇h(x) ∈ ∂g(S_f(x, η))
-- statement:
--   Let $V$ be a real Hilbert space, $h\in\mathcal S^{1,1}_{\mu,L}$ with $0\le\mu\le L<\infty$, $g:V\to\mathbb R\cup\{+\infty\}$ proper, closed and convex, and $\eta>0$. For $x\in V$ let $S_f(x,\eta)=\operatorname{prox}_{\eta g}(x-\eta\nabla h(x))$ and $\mathcal G_f(x,\eta)=(x-S_f(x,\eta))/\eta$ be the composite gradient mapping (111). Then
--   $$\mathcal G_f(x,\eta)-\nabla h(x)\in\partial g\big(S_f(x,\eta)\big).$$
--
--   The inclusion says that $-\mathcal G_f(x,\eta)$ is a subgradient-type direction of $f=h+g$ evaluated in a split way, which is why $\mathcal G_f$ plays the role of $\nabla f$ in the nonsmooth scheme.
--
--   **Formalization Note.** $S_f(x,\eta)$ is a named point satisfying the prox predicate. $g$ is encoded by $(g,D)$ as in the definitions file. The class of $h$ is the standing assumption of (110); the inclusion itself only uses the value $\nabla h(x)$.
-- source:
--   Luo & Chen, arXiv:1909.03145v4, §7.2.1, (111) and (113), p. 29

import Mathlib
import Definitions.Def_NAGFlow_APGM_Setting

namespace NAGFlow.APGM

/-- Inclusion (113) (Luo & Chen, arXiv:1909.03145v4, §7.2.1, p. 29). Let `h ∈ S^{1,1}_{μ,L}` with
`0 ≤ μ ≤ L < ∞`, `g : V → ℝ ∪ {+∞}` proper, closed and convex (encoded by `(g, D)`), `η > 0` and
`x ∈ V`. If `s = S_f(x, η) = prox_{ηg}(x − η∇h(x))`, then
`G_f(x, η) − ∇h(x) ∈ ∂g(S_f(x, η))`, where `G_f(x, η) = (x − S_f(x, η))/η`. -/
theorem eq_113 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (h : V → ℝ) (gradh : V → V) (μ L : ℝ) (hh : NAGFlow.PredCorr.IsS11 h gradh μ L)
    (g : V → ℝ) (D : Set V) (hg : IsProperClosedConvex g D) (η : ℝ) (hη : 0 < η)
    (x s : V) (hs : IsSf gradh g D η x s) :
    gradMap η x s - gradh x ∈ subdiff g D s := by sorry

end NAGFlow.APGM
