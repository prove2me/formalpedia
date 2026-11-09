-- Prove2me | Theorems.Thm_OnlinePerceptronIsolation_Binary_lemma_A_5
-- name    : OnlinePerceptronIsolation.Binary.lemma_A_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:56:33.055257+00:00
-- url     : https://prove2.me/theorems/6c4abfee-11b9-4dd9-bcaa-03b9e033fab5
-- title:
--   Lemma A.5 — all four Berry-Esseen hypotheses hold
-- statement:
--   There is a universal $K\ge1$ such that the following holds for every $m,r\ge3$ and measurable sign map $\phi:\mathbb R^m\to\{-1,+1\}$. Under independent $Y_i\sim N(0,I_m)$, define $S_i=\phi(Y_i)Y_i$, $W_i=S_i-\mathbb ES_i$, $W=r^{-1/2}\sum_iW_i$, $\Sigma=\operatorname{Cov}(W)$, $\sigma_j=\sqrt{\Sigma_{jj}}$, and $R_{jk}=\Sigma_{jk}/(\sigma_j\sigma_k)$. Then all four conclusions hold:
--
--   1. The vectors $W_i$ are independent and identically distributed.
--   2. Every $\Sigma_{jj}$ is strictly positive and finite.
--   3. Every coordinate satisfies $\|W_{ij}/\sigma_j\|_{\psi_2}\le K$.
--   4. For $b=1-2/\pi>0$, $\lambda_{\min}(R)\ge b$.
--
--   The spectral conclusion is displayed equivalently as
--   $$\forall x\in\mathbb R^m,\quad x^TRx\ge(1-2/\pi)\sum_jx_j^2.$$
--   The psi norm is the extended-valued infimum defined by $\mathbb E\exp(X^2/c^2)\le2$, with finite exponential moments. All moments and covariance entries are computed from the Gaussian samples. None of these four conclusions is assumed; together they supply the hypotheses of the approximation theorem.
--
--   Differences from the source:
--   - encoding: one-based sign cube and coordinates → zero-based Fin indices and exact real-valued signs; reason: a bijection of coordinate labels preserves every signing and Hamming distance
--   - encoding: a universal positive spectral constant b → the proof value b equals 1-2/pi; reason: equations (A.42) and (A.46)-(A.51) establish this value
--   - encoding: a lower bound on the smallest eigenvalue of the symmetric correlation matrix → the equivalent Euclidean quadratic-form inequality; reason: the covariance-derived matrix is symmetric
--   - encoding: the psi2 bound on the first summand and finite real variances → the same bound for every identically distributed summand, using the extended Orlicz norm and real covariance entries; reason: identical distributions make these bounds equivalent; the extended norm prevents empty-infimum defaults
--   - encoding: correlation matrix D inverse Sigma D inverse → the referenced coefficient Sigma_ij divided by sqrt(Sigma_ii times Sigma_jj); reason: positive covariance diagonals make sqrt of the product equal the product of standard deviations
-- source:
--   Shuangping Li, Gabe Schoenbach, STOC 2027 submission #485 (October 2026), Lemma A.5, Eq. (A.32), printed pp.21-22, PDF pp.23-24; proof Eqs. (A.33)-(A.51), printed pp.22-23, PDF pp.24-25; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/485.pdf

import Mathlib
import Definitions.Def_OnlinePerceptronIsolation_Binary_SignedGaussian
import Definitions.Def_OnlinePerceptronIsolation_Binary_Correlation
import Definitions.Def_HighDimProb_Concentration_SubgaussianNorm_v2
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace OnlinePerceptronIsolation.Binary

/-- Lemma A.5, printed pp.21--22 / PDF pp.23--24. All four clauses are conclusions;
(A.42),(A.50)--(A.51) supply b=1-2/π. K is chosen before all instance data. -/
theorem lemma_A_5 : ∃ K : ℝ, 1 ≤ K ∧
    ∀ (m r : ℕ), 3 ≤ m → 3 ≤ r →
      ∀ (ϕ : (Fin m → ℝ) → ℝ), Measurable ϕ →
        (∀ y, ϕ y = 1 ∨ ϕ y = -1) →
        let P := ABPOnline.gaussMat m r
        let X := centeredColumn (r := r) ϕ
        let S := covMatrix P (normalizedSum X)
        iIndepFun X P ∧
        (∀ i k : Fin r, IdentDistrib (X i) (X k) P P) ∧
        (∀ j : Fin m, 0 < S j j) ∧
        (∀ (i : Fin r) (j : Fin m),
          HighDimProb.Concentration.subgaussianNorm P
            (fun Y => X i Y j / marginalSD S j) ≤ ENNReal.ofReal K) ∧
        0 < (1 - 2 / Real.pi : ℝ) ∧
        HasSpectralLowerBound (CODATA.corr S) (1 - 2 / Real.pi) := by sorry

end OnlinePerceptronIsolation.Binary
