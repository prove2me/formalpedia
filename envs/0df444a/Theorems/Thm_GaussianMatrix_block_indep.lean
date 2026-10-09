-- Prove2me | Theorems.Thm_GaussianMatrix_block_indep
-- name    : GaussianMatrix.block_indep
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T02:27:14.23151+00:00
-- url     : https://prove2.me/theorems/2afcf97e-496a-4ad4-88e8-3f8e06594929
-- title:
--   Independence of the blocks $V_1^{\mathsf T}\Omega$ and $V_2^{\mathsf T}\Omega$ for orthonormal frames with $V_1^{\mathsf T}V_2=0$
-- statement:
--   Let $\Omega\in\mathbb R^{n\times t}$ be a standard Gaussian matrix and let $V_1\in\mathbb R^{n\times k}$, $V_2\in\mathbb R^{n\times r}$ have orthonormal columns ($V_1^{\mathsf T}V_1=I_k$, $V_2^{\mathsf T}V_2=I_r$) spanning orthogonal subspaces ($V_1^{\mathsf T}V_2=0$). Then the random matrices
--   $$\Omega_1=V_1^{\mathsf T}\Omega\qquad\text{and}\qquad \Omega_2=V_2^{\mathsf T}\Omega$$
--   are stochastically independent.
--
--   Together with the law of each block, this justifies conditioning on $\Omega_1$ while treating $\Omega_2$ as a fresh standard Gaussian matrix — the step that turns the deterministic range-finder bound $\|\Sigma_2\Omega_2\Omega_1^{\dagger}\|_F$ into an explicit expectation.
--
--   **Formalization Note.** Independence is Mathlib's `IndepFun` of the two measurable maps $\Omega\mapsto V_1^{\mathsf T}\Omega$ and $\Omega\mapsto V_2^{\mathsf T}\Omega$ under $\gamma_{n,t}$. The frames need not be complete: $k+r\le n$ is allowed to be strict.
-- source:
--   N. Halko, P.-G. Martinsson, J. A. Tropp, *Finding structure with randomness: probabilistic algorithms for constructing approximate matrix decompositions*, SIAM Review 53(2), 2011, https://arxiv.org/abs/0909.4061 (v2), §10.2 p. 57, proof of Theorem 10.5: "Observe that Ω₁ and Ω₂ are nonoverlapping submatrices of V*Ω, so these two matrices are not only standard Gaussian but also stochastically independent." (second claim)

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix
theorem block_indep {n k r t : ℕ} (V₁ : Matrix (Fin n) (Fin k) ℝ) (V₂ : Matrix (Fin n) (Fin r) ℝ)
    (hV₁ : V₁ᵀ * V₁ = 1) (hV₂ : V₂ᵀ * V₂ = 1) (hV₁₂ : V₁ᵀ * V₂ = 0) :
    IndepFun (fun G : Fin n → Fin t → ℝ => Matrix.of.symm (V₁ᵀ * Matrix.of G))
      (fun G : Fin n → Fin t → ℝ => Matrix.of.symm (V₂ᵀ * Matrix.of G)) (gaussianMatrix n t) := by sorry
end GaussianMatrix
