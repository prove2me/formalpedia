-- Prove2me | Theorems.Thm_NestedSA_NASA_eq_3_21
-- name    : NestedSA.NASA.eq_3_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:38:51.566957+00:00
-- url     : https://prove2.me/theorems/bf57e45d-6ade-473e-bb72-dae49d6e57b0
-- title:
--   (3.21) — the subproblem step satisfies ⟨z,d⟩ + β‖d‖² ≤ 0
-- statement:
--   Let $X\subseteq\mathbb R^n$ be closed and convex, $x\in X$, $z\in\mathbb R^n$, $\beta>0$, and let $d=\bar y(x,z,\beta)-x$ be the step of subproblem (2.5), where $\bar y(x,z,\beta)=\Pi_X(x-\frac1\beta z)$. Then
--   $$\langle z,d\rangle+\beta\|d\|^2\le0.$$
--
--   This consequence of the optimality condition of (2.5) gives $\eta(x,z)\le0$ on $X$, hence $W\ge0$, and the bound $\beta\|d\|\le\|z\|$ used in Proposition 1.
-- source:
--   Ghadimi, Ruszczyński, Wang, A Single Time-Scale Stochastic Approximation Method for Nested Stochastic Optimization, arXiv:1812.01094v2, §3, proof of Lemma 4, (3.21), p. 11

import Mathlib
import Definitions.Def_SpectralProjGrad_Shared_IsProjOnto
import Definitions.Def_NestedSA_NASA_Basic

open scoped RealInnerProductSpace

namespace NestedSA.NASA

/-- (3.21) (p. 11, proof of Lemma 4): for a closed convex `X` with Euclidean projection `P`, every `x ∈ X`, every
`z` and every `β > 0`, the step `d = ȳ(x, z, β) − x` satisfies `⟨z, d⟩ + β‖d‖² ≤ 0`. -/
theorem eq_3_21 {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (hX_cl : IsClosed X) (hX_cvx : Convex ℝ X)
    (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hP : SpectralProjGrad.Shared.IsProjOnto X P)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ X) (z : EuclideanSpace ℝ (Fin n)) (β : ℝ) (hβ : 0 < β) :
    ⟪z, ybar P x z β - x⟫ + β * ‖ybar P x z β - x‖ ^ 2 ≤ 0 := by sorry

end NestedSA.NASA
