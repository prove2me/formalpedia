-- Prove2me | Theorems.Thm_MifflinSemismooth_Optimality_minimizer_of_zero_mem
-- name    : MifflinSemismooth.Optimality.minimizer_of_zero_mem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:48:08.580986+00:00
-- url     : https://prove2.me/theorems/47a25d62-c554-4765-ad31-385fbff30d19
-- title:
--   Proof of Theorem 9, p. 20 — F semiconvex at x̄ w.r.t. Rⁿ and 0 ∈ ∂F(x̄) imply x̄ minimizes F over Rⁿ
-- statement:
--   Let $F:\mathbb R^n\to\mathbb R$ be semiconvex at $\bar x$ with respect to $X=\mathbb R^n$, and suppose $0\in\partial F(\bar x)$. Then $\bar x$ is a global minimizer of $F$:
--   $$
--   F(\bar x)\le F(x)\qquad\text{for all } x\in\mathbb R^n.
--   $$
--
--   In the proof of Theorem 9 this is applied to $h$ when $h(\bar x)>0$ (giving part (a)), to $f$ when $h(\bar x)<0$ (giving part (b)(i)), and to $h$ when $h(\bar x)=0$ and $\lambda=0$ (giving part (b)(ii)).
--
--   **Formalization Note** The page states the step separately for $h$ and for $f$; it is stated once here for a generic $F$. Semiconvexity is assumed only at $\bar x$ (with respect to $\mathbb R^n$), which is all the step uses.
-- source:
--   Mifflin, Semismooth and semiconvex functions in constrained optimization, IIASA Research Report RR-76-21 (December 1976), p. 20, §5, proof of Theorem 9, first two sentences

import Mathlib
import Definitions.Def_MifflinSemismooth_Optimality_Setting

namespace MifflinSemismooth.Optimality

/-- Mifflin (1976), §5, proof of Theorem 9, p. 20: if `F` is semiconvex at `x̄` with respect to
`ℝⁿ` and `0 ∈ ∂F(x̄)`, then `x̄` minimizes `F` over `ℝⁿ`. -/
theorem minimizer_of_zero_mem {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (xbar : EuclideanSpace ℝ (Fin n)) (hF : MifflinSemismooth.Extremal.SemiconvexAt Set.univ F xbar)
    (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ MifflinSemismooth.Extremal.genGrad F xbar) :
    ∀ x, F xbar ≤ F x := by sorry

end MifflinSemismooth.Optimality
