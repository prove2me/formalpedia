-- Prove2me | Theorems.Thm_NAGFlow_APGM_lemma_7_1
-- name    : NAGFlow.APGM.lemma_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:31:21.502996+00:00
-- url     : https://prove2.me/theorems/2e195695-adfd-4c41-8cbf-13270a752748
-- title:
--   Lemma 7.1, p. 29 — f(y) ≥ f(S_f(x)) + ⟨G_f(x), y − x⟩ + (μ/2)‖y − x‖² + ‖G_f(x)‖²/(2L)
-- statement:
--   Let $V$ be a real Hilbert space and $f=h+g$, where $h\in\mathcal S^{1,1}_{\mu,L}$ with $0\le\mu\le L<\infty$ and $g:V\to\mathbb R\cup\{+\infty\}$ is proper, closed and convex. Write $S_f(x)=\operatorname{prox}_{g/L}(x-\frac1L\nabla h(x))$ and $\mathcal G_f(x)=L(x-S_f(x))$. Then for every $x\in V$ and every $y\in\operatorname{dom}g$,
--   $$f(y)\ \ge\ f(S_f(x))+\langle\mathcal G_f(x),y-x\rangle+\frac\mu2\|y-x\|^2+\frac1{2L}\|\mathcal G_f(x)\|^2.\qquad(114)$$
--
--   The right-hand side is a quadratic lower model of $f$ at $x$ built from the gradient mapping; it is the composite analogue of $\mu$-convexity plus the descent lemma, and it is the only property of $g$ used in the convergence proof of Algorithm 2.
--
--   **Formalization Note.** The page says "for any $x,y\in V$"; for $y\notin\operatorname{dom}g$ its left side is $+\infty$ and (114) is void, so the statement is made for $y\in\operatorname{dom}g$. $S_f(x)$ is a named point satisfying the prox predicate with $\eta=1/L$. $\langle\cdot,\cdot\rangle$ is the inner product of $V$ (Riesz).
-- source:
--   Luo & Chen, arXiv:1909.03145v4, Lemma 7.1 and (114), p. 29

import Mathlib
import Definitions.Def_NAGFlow_APGM_Setting

namespace NAGFlow.APGM

/-- Lemma 7.1 (Luo & Chen, arXiv:1909.03145v4, p. 29). Assume `f = h + g`, where `h ∈ S^{1,1}_{μ,L}`
with `0 ≤ μ ≤ L < ∞` and `g : V → ℝ ∪ {+∞}` is proper, closed and convex (encoded by `(g, D)`,
`D = dom g`). Then for any `x ∈ V` and any `y ∈ dom g` (for `y ∉ dom g` the page's `f(y) = +∞` and the
inequality is void), with `S_f(x) = prox_{g/L}(x − ∇h(x)/L)` and `G_f(x) = L(x − S_f(x))`,
`f(y) ≥ f(S_f(x)) + ⟪G_f(x), y − x⟫ + (μ/2)‖y − x‖² + (1/(2L))‖G_f(x)‖²`  (114). -/
theorem lemma_7_1 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (h : V → ℝ) (gradh : V → V) (μ L : ℝ) (hh : NAGFlow.PredCorr.IsS11 h gradh μ L)
    (g : V → ℝ) (D : Set V) (hg : IsProperClosedConvex g D)
    (x y s : V) (hy : y ∈ D) (hs : IsSf gradh g D (1 / L) x s) :
    (h + g) y ≥ (h + g) s + inner ℝ (gradMap (1 / L) x s) (y - x) + μ / 2 * ‖y - x‖ ^ 2
      + 1 / (2 * L) * ‖gradMap (1 / L) x s‖ ^ 2 := by sorry

end NAGFlow.APGM
