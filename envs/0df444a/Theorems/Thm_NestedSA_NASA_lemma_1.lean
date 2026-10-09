-- Prove2me | Theorems.Thm_NestedSA_NASA_lemma_1
-- name    : NestedSA.NASA.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:38:48.724508+00:00
-- url     : https://prove2.me/theorems/1ea98200-0de9-464d-9797-765b183e704c
-- title:
--   Lemma 1 — the unit-step projected displacement is at most max(1,β) times the β-step one
-- statement:
--   Let $X\subseteq\mathbb R^n$ be closed and convex, $\Pi_X$ the Euclidean projection onto $X$, and $\bar y(x,z,\beta)=\Pi_X(x-\frac1\beta z)$ the solution of subproblem (2.5). For every $x\in X$, every $z\in\mathbb R^n$ and every $\beta>0$,
--   $$\|\bar y(x,z,1)-x\|\le\max(1,\beta)\,\|\bar y(x,z,\beta)-x\|.$$
--
--   The lemma compares the step of the subproblem at an arbitrary regularization $\beta$ with the unit-regularization step that enters the optimality measure $V$; it is what turns a bound on the algorithm's steps into a bound on $V$.
-- source:
--   Ghadimi, Ruszczyński, Wang, A Single Time-Scale Stochastic Approximation Method for Nested Stochastic Optimization, arXiv:1812.01094v2, p. 7, Lemma 1, (2.11)

import Mathlib
import Definitions.Def_SpectralProjGrad_Shared_IsProjOnto
import Definitions.Def_NestedSA_NASA_Basic

namespace NestedSA.NASA

/-- Lemma 1, (2.11) (p. 7): for a closed convex `X ⊆ ℝⁿ` with Euclidean projection `P`, every `x ∈ X`, every
`z ∈ ℝⁿ` and every `β > 0`, `‖ȳ(x, z, 1) − x‖ ≤ max(1, β) ‖ȳ(x, z, β) − x‖`, where `ȳ(x, z, β) = Π_X(x − β⁻¹z)`. -/
theorem lemma_1 {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (hX_cl : IsClosed X) (hX_cvx : Convex ℝ X)
    (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hP : SpectralProjGrad.Shared.IsProjOnto X P)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ X) (z : EuclideanSpace ℝ (Fin n)) (β : ℝ) (hβ : 0 < β) :
    ‖ybar P x z 1 - x‖ ≤ max 1 β * ‖ybar P x z β - x‖ := by sorry

end NestedSA.NASA
