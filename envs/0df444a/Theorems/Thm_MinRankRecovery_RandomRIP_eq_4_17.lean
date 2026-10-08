-- Prove2me | Theorems.Thm_MinRankRecovery_RandomRIP_eq_4_17
-- name    : MinRankRecovery.RandomRIP.eq_4_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:17:50.946995+00:00
-- url     : https://prove2.me/theorems/c0b2edbc-873f-4904-86ce-46687008703b
-- title:
--   (4.17) — ρ(Σ(V₁, W₁), Σ(V₂, W₂)) ≤ ρ(V₁, V₂) + ρ(W₁, W₂)
-- statement:
--   Let $V_1,V_2\subseteq\mathbb R^m$ and $W_1,W_2\subseteq\mathbb R^n$ be subspaces, and let $\Sigma(V,W)$ denote the subspace of $m\times n$ matrices with column space in $V$ and row space in $W$. Then
--   $$\rho\big(\Sigma(V_1,W_1),\Sigma(V_2,W_2)\big)\le\rho(V_1,V_2)+\rho(W_1,W_2),$$
--   where $\rho$ is the projection distance (the operator norm of the difference of orthogonal projections), computed in $\mathbb R^{m\times n}$ with the Frobenius inner product on the left and in $\mathbb R^m$, $\mathbb R^n$ on the right.
--
--   The inequality reduces covering the family of subspaces $\Sigma(V,W)$ to covering the two Grassmannians separately, and is the first step of the paper's covering-number bound.
--
--   **Formalization Note** Matrices are vectorized in `EuclideanSpace ℝ (Fin m × Fin n)`. No dimension hypotheses are imposed; the printed chain holds for arbitrary subspaces.
-- source:
--   Recht, Fazel & Parrilo, arXiv:0706.4138v1, §4, proof of Lemma 4.5, (4.17), p. 18

import Mathlib
import Definitions.Def_MinRankRecovery_RandomRIP_SubspaceDist

namespace MinRankRecovery.RandomRIP

/-- (4.17), p. 18, proof of Lemma 4.5: for subspaces `V₁, V₂ ⊆ ℝᵐ` and `W₁, W₂ ⊆ ℝⁿ`,
`ρ(Σ(V₁, W₁), Σ(V₂, W₂)) ≤ ρ(V₁, V₂) + ρ(W₁, W₂)`. -/
theorem eq_4_17 {m n : ℕ} (V₁ V₂ : Submodule ℝ (EuclideanSpace ℝ (Fin m)))
    (W₁ W₂ : Submodule ℝ (EuclideanSpace ℝ (Fin n))) :
    projDist (sigmaSub V₁ W₁) (sigmaSub V₂ W₂) ≤ projDist V₁ V₂ + projDist W₁ W₂ := by sorry

end MinRankRecovery.RandomRIP
