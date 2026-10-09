-- Prove2me | Theorems.Thm_GaussianMatrix_rotation_invariance
-- name    : GaussianMatrix.rotation_invariance
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T02:26:23.959305+00:00
-- url     : https://prove2.me/theorems/c13db467-cbac-4e39-851c-e98484661d88
-- title:
--   Rotational invariance of the standard Gaussian matrix: $U\Gamma V\sim\Gamma$ for orthogonal $U,V$
-- statement:
--   Let $\Gamma\in\mathbb R^{p\times m}$ be a standard Gaussian matrix (independent $\mathcal N(0,1)$ entries, law $\gamma_{p,m}$), and let $U\in\mathbb R^{p\times p}$ and $V\in\mathbb R^{m\times m}$ be orthogonal matrices, $U^{\mathsf T}U=I_p$ and $V^{\mathsf T}V=I_m$. Then the matrix $U\Gamma V$ is again a standard Gaussian matrix:
--   $$U\,\Gamma\,V\ \sim\ \gamma_{p,m}.$$
--
--   This is the basic symmetry of the Gaussian ensemble. It lets one reduce computations involving fixed matrices $S\Gamma T$ to the case of diagonal $S$ and $T$, and it is the engine behind every conditioning argument in the analysis of randomized sketching: multiplying a Gaussian sketch by an orthogonal factor of the input matrix does not change its law.
--
--   **Formalization Note.** The statement is an equality of measures: the pushforward of $\gamma_{p,m}$ under $G\mapsto UGV$ equals $\gamma_{p,m}$.
-- source:
--   N. Halko, P.-G. Martinsson, J. A. Tropp, *Finding structure with randomness: probabilistic algorithms for constructing approximate matrix decompositions*, SIAM Review 53(2), 2011, https://arxiv.org/abs/0909.4061 (v2), §10.1 p. 55: "The distribution of a standard Gaussian matrix is rotationally invariant: If U and V are orthonormal matrices, then U*GV also has the standard Gaussian distribution."

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix
theorem rotation_invariance {p m : ℕ} (U : Matrix (Fin p) (Fin p) ℝ) (V : Matrix (Fin m) (Fin m) ℝ)
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) :
    Measure.map (fun G : Fin p → Fin m → ℝ => Matrix.of.symm (U * Matrix.of G * V))
      (gaussianMatrix p m) = gaussianMatrix p m := by sorry
end GaussianMatrix
