-- Prove2me | Theorems.Thm_GaussianMatrix_block_law
-- name    : GaussianMatrix.block_law
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T02:26:44.854581+00:00
-- url     : https://prove2.me/theorems/e598d6e3-0620-4fb6-b255-5f8b4a34b2fa
-- title:
--   Law of a block $V_1^{\mathsf T}\Omega$ of a Gaussian matrix under an orthonormal frame
-- statement:
--   Let $\Omega\in\mathbb R^{n\times t}$ be a standard Gaussian matrix and let $V_1\in\mathbb R^{n\times k}$ have orthonormal columns, $V_1^{\mathsf T}V_1=I_k$. Then
--   $$V_1^{\mathsf T}\Omega\ \sim\ \gamma_{k,t},$$
--   i.e. $V_1^{\mathsf T}\Omega$ is a standard Gaussian $k\times t$ matrix.
--
--   In the analysis of the randomized SVD one writes the right singular vectors of the input as $[V_1\ V_2]$ and works with $\Omega_1=V_1^{\mathsf T}\Omega$; this statement says $\Omega_1$ is itself standard Gaussian, so the moment identities and singular-value tail bounds for Gaussian matrices apply to it directly.
--
--   **Formalization Note.** The statement is an equality of measures: the pushforward of $\gamma_{n,t}$ under $\Omega\mapsto V_1^{\mathsf T}\Omega$ equals $\gamma_{k,t}$. The hypothesis $V_1^{\mathsf T}V_1=I_k$ forces $k\le n$.
-- source:
--   N. Halko, P.-G. Martinsson, J. A. Tropp, *Finding structure with randomness: probabilistic algorithms for constructing approximate matrix decompositions*, SIAM Review 53(2), 2011, https://arxiv.org/abs/0909.4061 (v2), §10.2 p. 57, proof of Theorem 10.5: "The Gaussian distribution is rotationally invariant, so V*Ω is also a standard Gaussian matrix. Observe that Ω₁ and Ω₂ are nonoverlapping submatrices of V*Ω, so these two matrices are not only standard Gaussian but also stochastically independent." (first claim)

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix
theorem block_law {n k t : ℕ} (V₁ : Matrix (Fin n) (Fin k) ℝ) (hV₁ : V₁ᵀ * V₁ = 1) :
    Measure.map (fun G : Fin n → Fin t → ℝ => Matrix.of.symm (V₁ᵀ * Matrix.of G))
      (gaussianMatrix n t) = gaussianMatrix k t := by sorry
end GaussianMatrix
