-- Prove2me | Theorems.Thm_OnlinePerceptronIsolation_Binary_theorem_A_1
-- name    : OnlinePerceptronIsolation.Binary.theorem_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:55:17.635166+00:00
-- url     : https://prove2.me/theorems/9a8d8def-43a6-4591-8b76-a5a22be2ebd6
-- title:
--   Theorem A.1 — high-dimensional Berry-Esseen bound
-- statement:
--   Fix $K\ge1$ and $b>0$. There is $C=C(K,b)>0$ such that for every $m,r\ge3$ and independent, identically distributed, centered measurable vectors $X_1,\ldots,X_r\in\mathbb R^m$ on any probability space, the following implication holds. Put $W=r^{-1/2}\sum_iX_i$, $\Sigma=\operatorname{Cov}(W)$, $\sigma_j=\sqrt{\Sigma_{jj}}$, and $R_{jk}=\Sigma_{jk}/(\sigma_j\sigma_k)$. Suppose $0<\Sigma_{jj}<\infty$, $\|X_{1j}/\sigma_j\|_{\psi_2}\le K$ for every $j$, and $\lambda_{\min}(R)\ge b$. For $Z\sim N(0,\Sigma)$,
--   $$\sup_{A\in\mathcal R_m}|\mathbb P(W\in A)-\mathbb P(Z\in A)|\le C\frac{(\log m)^{3/2}\log r+(\log m)^2}{\sqrt r},$$
--   where $\mathcal R_m$ contains every product $\prod_j[a_j,c_j)$ with $-\infty\le a_j\le c_j\le+\infty$. The Gaussian law is constructed from the actual covariance, and the bound is uniform over the probability space, dimensions, vector law, and rectangles. This is the quantitative approximation used after A.5.
--
--   Differences from the source:
--   - encoding: the supremum over all half-open extended-endpoint rectangles → the identical bound for every such rectangle; reason: all errors lie in [0,1], so the pointwise family of inequalities is equivalent to the supremum inequality
--   - encoding: a centered Gaussian with the computed covariance → Mathlib multivariateGaussian of zero mean and that covariance on EuclideanSpace; reason: actual covariance is positive semidefinite; this constructs the stated Gaussian
--   - encoding: the smallest eigenvalue bound and first-summand psi2 bounds → the equivalent quadratic-form bound and psi2 bounds for every identically distributed summand; reason: the matrix is symmetric and identical distributions give the same norm
--   - encoding: finite psi2 norm with the stated exponential-moment convention → the published extended-valued Orlicz norm; reason: this is the same infimum with infinite moments excluded and an empty admissible set assigned infinity
--   - encoding: the implicit O constant under fixed K and b → a positive C chosen after K and b and before all other data; reason: the source prints no numerical constant; this preserves its exact uniform rate
--   - encoding: correlation matrix D inverse Sigma D inverse → the referenced coefficient Sigma_ij divided by sqrt(Sigma_ii times Sigma_jj); reason: positive covariance diagonals make sqrt of the product equal the product of standard deviations
-- source:
--   Shuangping Li, Gabe Schoenbach, STOC 2027 submission #485 (October 2026), Theorem A.1, Eqs. (A.1)-(A.3), printed p.18, PDF p.20; proof printed p.19, PDF p.21; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/485.pdf

import Mathlib
import Definitions.Def_OnlinePerceptronIsolation_Binary_Correlation
import Definitions.Def_OnlinePerceptronIsolation_Binary_Rectangles
import Definitions.Def_HighDimProb_Concentration_SubgaussianNorm_v2
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace OnlinePerceptronIsolation.Binary

/-- Theorem A.1, printed p.18 / PDF p.20. The approximation constant depends only on
fixed K,b. Pointwise bounds over every extended-endpoint rectangle equal the stated sup bound. -/
theorem theorem_A_1 (K b : ℝ) (hK : 1 ≤ K) (hb : 0 < b) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (m r : ℕ), 3 ≤ m → 3 ≤ r →
        ∀ X : Fin r → Ω → Fin m → ℝ,
          (∀ i, Measurable (X i)) → iIndepFun X P →
          (∀ i k : Fin r, IdentDistrib (X i) (X k) P P) →
          (∀ (i : Fin r) (j : Fin m), ∫ ω, X i ω j ∂P = 0) →
          let S := covMatrix P (normalizedSum X)
          (∀ j : Fin m, 0 < S j j) →
          (∀ (i : Fin r) (j : Fin m),
            HighDimProb.Concentration.subgaussianNorm P
              (fun ω => X i ω j / marginalSD S j) ≤ ENNReal.ofReal K) →
          HasSpectralLowerBound (CODATA.corr S) b →
          ∀ a c : Fin m → EReal, (∀ j, a j ≤ c j) →
            |P.real {ω | normalizedSum X ω ∈ rectangle a c} -
              (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) S).real
                {z | (fun j => z j) ∈ rectangle a c}| ≤
              C * (((Real.log m) ^ (3 / 2 : ℝ) * Real.log r + (Real.log m) ^ 2) /
                Real.sqrt r) := by sorry

end OnlinePerceptronIsolation.Binary
