-- Prove2me | Theorems.Thm_LesHouchesWidth_gaussian_linear_image
-- name    : LesHouchesWidth.gaussian_linear_image
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T22:01:42.176062+00:00
-- url     : https://prove2.me/theorems/6968e07f-ca30-4072-895c-759d8bff31c4
-- title:
--   Proposition 4.3: linear images of Gaussian vectors are Gaussian
-- statement:
--   Let $W\sim\mathcal N(\mu,\Sigma)$ be a Gaussian vector in $\mathbb R^d$ with mean $\mu$ and positive semidefinite covariance $\Sigma$, and let $A\in\mathbb R^{k\times d}$ be a fixed matrix. Then
--   $$AW\sim\mathcal N\big(A\mu,\ A\Sigma A^{T}\big).$$
--
--   This is the step that makes the next layer of a network conditionally Gaussian given the previous one (Lemma 4.4).
--
--   **Formalization Note** The notes allow $A$ to be random and independent of $W$. The formal statement treats a deterministic $A$, from which the independent case follows by conditioning.
-- source:
--   Bahri, Hanin, Brossollet, Erba, Keup, Pacelli, Simon, *Les Houches Lectures on Deep Learning at Large & Infinite Width*, arXiv:2309.01592v3 (https://arxiv.org/abs/2309.01592), p. 34, Proposition 4.3 (Section 4.9.1).

import Mathlib
import Definitions.Def_LesHouchesWidth_GaussianMLP
import Definitions.Def_LesHouchesWidth_FiniteWidth

namespace LesHouchesWidth

open MeasureTheory ProbabilityTheory

theorem gaussian_linear_image {k d : ℕ} (μ : EuclideanSpace ℝ (Fin d))
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef) (A : Matrix (Fin k) (Fin d) ℝ) :
    (multivariateGaussian μ S).map (Matrix.toEuclideanLin A) =
      multivariateGaussian (Matrix.toEuclideanLin A μ) (A * S * A.transpose) := by sorry

end LesHouchesWidth
