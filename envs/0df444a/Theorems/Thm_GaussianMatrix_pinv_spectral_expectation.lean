-- Prove2me | Theorems.Thm_GaussianMatrix_pinv_spectral_expectation
-- name    : GaussianMatrix.pinv_spectral_expectation
-- status  : Open
-- author  : @tc
-- created : 2026-10-09T02:43:00.330918+00:00
-- url     : https://prove2.me/theorems/d4d3ca6e-eb6f-496c-b9cd-975119336270
-- title:
--   Expected spectral norm of a pseudo-inverted Gaussian matrix: $\mathbb E\|G^{\dagger}\|\le\frac{e\sqrt{k}}{k-r}$
-- statement:
--   Let $G\in\mathbb R^{r\times k}$ be a standard Gaussian matrix with $r\ge2$ and $k-r\ge1$, and let $G^{\dagger}=G^{\mathsf T}(GG^{\mathsf T})^{-1}$. Then $\|G^{\dagger}\|$ is integrable and
--   $$\mathbb E\,\|G^{\dagger}\|\ \le\ \frac{e\sqrt{k}}{k-r},$$
--   where $\|\cdot\|$ is the spectral norm.
--
--   In Halko–Martinsson–Tropp's notation ($G$ is $k\times(k+p)$) the bound reads $e\sqrt{k+p}/p$: it is the spectral inverse moment that, together with the Frobenius inverse moment, yields the expected spectral-norm error bound of the randomized SVD. Its proof integrates the Chen–Dongarra tail bound for $\|G^{\dagger}\|$.
--
--   **Formalization Note.** $G^{\dagger}$ is `pinvR` ($0$ on the null set where $GG^{\mathsf T}$ is singular). The conclusion is the conjunction of integrability and the bound.
-- source:
--   N. Halko, P.-G. Martinsson, J. A. Tropp, *Finding structure with randomness: probabilistic algorithms for constructing approximate matrix decompositions*, SIAM Review 53(2), 2011, https://arxiv.org/abs/0909.4061 (v2), §10.1 p. 55, Proposition 10.2 eq. (10.4) ($k\times(k+p)$, $k\ge2$, $p\ge2$: $\mathbb E\|G^\dagger\|\le e\sqrt{k+p}/p$) and Appendix A.2 p. 65, Proposition A.4 ($m\times n$ with $n-m\ge1$, $m\ge2$: $\mathbb E\|G^\dagger\|\le\frac{e\sqrt n}{n-m}$).

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix
theorem pinv_spectral_expectation {r k : ℕ} (hr : 2 ≤ r) (hrk : r + 1 ≤ k) :
    Integrable (fun G : Fin r → Fin k → ℝ => specNorm (pinvR (Matrix.of G))) (gaussianMatrix r k) ∧
    ∫ G, specNorm (pinvR (Matrix.of G)) ∂(gaussianMatrix r k)
      ≤ Real.exp 1 * Real.sqrt k / ((k : ℝ) - r) := by sorry
end GaussianMatrix
