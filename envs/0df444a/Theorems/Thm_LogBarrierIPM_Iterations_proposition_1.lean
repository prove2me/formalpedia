-- Prove2me | Theorems.Thm_LogBarrierIPM_Iterations_proposition_1
-- name    : LogBarrierIPM.Iterations.proposition_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T14:06:32.042916+00:00
-- url     : https://prove2.me/theorems/0d95df32-1355-4e0d-9d43-fc059670f273
-- title:
--   Proposition 1 — the duality measure is affine along lines through feasible points
-- statement:
--   Let $A\in\mathbb R^{m\times n}$, $b\in\mathbb R^m$, $c\in\mathbb R^n$, and let $z=(x,w,s,y)$ and $z'=(x',w',s',y')$ be two points of the primal-dual feasible set $\mathcal F=\{z\ge0:\ Ax+w=b,\ s-A^\top y=c\}$. Then for every $\alpha\in\mathbb R$,
--   $$\bar\mu\big((1-\alpha)z+\alpha z'\big)=(1-\alpha)\,\bar\mu(z)+\alpha\,\bar\mu(z'),$$
--   where $\bar\mu(z)=\frac1{n+m}(\langle x,s\rangle+\langle w,y\rangle)$ is the duality measure.
--
--   Although $\bar\mu$ is quadratic, it is affine on feasible lines. Along each segment of a path-following method the duality measure therefore varies monotonically between its values at the endpoints, which is used in the paper's general lower bound (Theorem 29).
--
--   **Formalization Note** $\alpha$ ranges over all reals, so $(1-\alpha)z+\alpha z'$ may leave the non-negative orthant; $\bar\mu$ is the same formula on all of $\mathbb R^{2N}$.
-- source:
--   Allamigeon, Benchimol, Gaubert, Joswig, Log-Barrier Interior Point Methods Are Not Strongly Polynomial, arXiv:1708.01544v2, p. 5, Proposition 1

import Mathlib
import Definitions.Def_LogBarrierIPM_Iterations_SlackLP

namespace LogBarrierIPM.Iterations

/-- Proposition 1 (p. 5). For two points `z, z'` of the primal-dual feasible set `F` of
`LP(A, b, c)`, `DualLP(A, b, c)` and every `α ∈ ℝ`,
`μ̄((1 − α) z + α z') = (1 − α) μ̄(z) + α μ̄(z')`. -/
theorem proposition_1 {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (z z' : PDPoint n m) (hz : z ∈ primalDualFeasible A b c)
    (hz' : z' ∈ primalDualFeasible A b c) (α : ℝ) :
    dualityMeasure ((1 - α) • z + α • z') =
      (1 - α) * dualityMeasure z + α * dualityMeasure z' := by sorry

end LogBarrierIPM.Iterations
