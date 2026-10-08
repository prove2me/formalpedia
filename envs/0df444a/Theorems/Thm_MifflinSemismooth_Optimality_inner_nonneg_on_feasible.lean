-- Prove2me | Theorems.Thm_MifflinSemismooth_Optimality_inner_nonneg_on_feasible
-- name    : MifflinSemismooth.Optimality.inner_nonneg_on_feasible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:48:09.145977+00:00
-- url     : https://prove2.me/theorems/7dcc36b4-f4c1-41fe-9fb4-d09b70062e11
-- title:
--   Proof of Theorem 9, p. 21 — if λ > 0 then ⟨ḡ, x − x̄⟩ ≧ 0 for all x with h(x) ≦ 0
-- statement:
--   Let $h:\mathbb R^n\to\mathbb R$ be semiconvex on $\mathbb R^n$ and let $\bar x$ satisfy $h(\bar x)=0$. Let $0<\lambda\le 1$, $\bar g\in\mathbb R^n$ and $\hat g\in\partial h(\bar x)$ with $\lambda\bar g+(1-\lambda)\hat g=0$. Then
--   $$
--   \langle\bar g,\,x-\bar x\rangle\ge 0\qquad\text{for all } x \text{ with } h(x)\le 0 .
--   $$
--
--   Combined with the semiconvexity of $f$ and $\bar g\in\partial f(\bar x)$, this inequality shows $f(x)\ge f(\bar x)$ on the feasible set, i.e. that $\bar x$ is optimal when $\lambda>0$.
--
--   **Formalization Note** The membership $\bar g\in\partial f(\bar x)$ of the page's setting is not needed for this step and is not assumed; dropping it makes the statement stronger, not weaker.
-- source:
--   Mifflin, Semismooth and semiconvex functions in constrained optimization, IIASA Research Report RR-76-21 (December 1976), p. 21, §5, proof of Theorem 9, case λ > 0

import Mathlib
import Definitions.Def_MifflinSemismooth_Optimality_Setting

namespace MifflinSemismooth.Optimality

/-- Mifflin (1976), §5, proof of Theorem 9, p. 21: if `h` is semiconvex on `ℝⁿ`, `h(x̄) = 0`,
`0 < λ ≤ 1`, `ĝ ∈ ∂h(x̄)` and `λ ḡ + (1 - λ) ĝ = 0`, then `⟨ḡ, x - x̄⟩ ≥ 0` for every `x` with
`h(x) ≤ 0`. -/
theorem inner_nonneg_on_feasible {n : ℕ} (h : EuclideanSpace ℝ (Fin n) → ℝ)
    (hh : MifflinSemismooth.Extremal.SemiconvexOn Set.univ h) (xbar : EuclideanSpace ℝ (Fin n)) (hzero : h xbar = 0)
    (lam : ℝ) (gbar ghat : EuclideanSpace ℝ (Fin n)) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hghat : ghat ∈ MifflinSemismooth.Extremal.genGrad h xbar) (hcomb : lam • gbar + (1 - lam) • ghat = 0) :
    ∀ x, h x ≤ 0 → 0 ≤ inner ℝ gbar (x - xbar) := by sorry

end MifflinSemismooth.Optimality
