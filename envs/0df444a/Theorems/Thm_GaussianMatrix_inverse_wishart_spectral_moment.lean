-- Prove2me | Theorems.Thm_GaussianMatrix_inverse_wishart_spectral_moment
-- name    : GaussianMatrix.inverse_wishart_spectral_moment
-- status  : Open
-- author  : @tc
-- created : 2026-10-09T02:43:48.364759+00:00
-- url     : https://prove2.me/theorems/b8bbfa46-4e40-44b1-acd8-87ddb9ac6bb3
-- title:
--   Tropp–Webber inverse spectral moment: $(\mathbb E\|(GG^{\mathsf T})^{-1}\|^p)^{1/p}\le\frac{e^2(k+r)}{2(k-r)^2}$ for $1\le p\le18$, $k\ge r+2p$
-- statement:
--   Let $G\in\mathbb R^{r\times k}$ be a standard Gaussian matrix, let $p$ be an integer with $1\le p\le18$, and assume $k\ge r+2p$. Then $\|(GG^{\mathsf T})^{-1}\|^p$ is integrable and
--   $$\Bigl(\mathbb E\,\bigl\|(GG^{\mathsf T})^{-1}\bigr\|^p\Bigr)^{1/p}\ \le\ \frac{e^2\,(k+r)}{2\,(k-r)^2},$$
--   where $\|\cdot\|$ is the spectral norm. Since $\|(GG^{\mathsf T})^{-1}\|=\|G^{\dagger}\|^2=\sigma_{\min}(G)^{-2}$, this bounds the $2p$-th inverse moment of the smallest singular value of a Gaussian matrix.
--
--   The case $p=1$, $\mathbb E\|G^{\dagger}\|^2\le e^2(k+r)/(2(k-r)^2)$, is the spectral-norm input for expected spectral-norm error bounds of the randomized SVD and of truncated sketching algorithms, where it is combined with the Frobenius inverse moment $\mathbb E\|G^{\dagger}\|_F^2=r/(k-r-1)$. The proof in the source starts from Edelman's bound on the density of $\lambda_{\min}(GG^{\mathsf T})$.
--
--   **Formalization Note.** The bound is stated in the equivalent form $\mathbb E\|(GG^{\mathsf T})^{-1}\|^p\le\bigl(e^2(k+r)/(2(k-r)^2)\bigr)^p$, together with integrability of the integrand. The source writes the hypothesis as $k\ge r+2m$ with $m$ the moment order (a typographical variant of $p$); its proof uses exactly $k-r\ge2p$.
-- source:
--   J. A. Tropp, R. J. Webber, *Randomized algorithms for low-rank matrix approximation: design, analysis, and applications*, 2023, https://arxiv.org/abs/2306.12418 (v1), Appendix B p. 52, Lemma B.3 (Inverse moment bounds, spectral norm), eq. (B.4): for $0\le p\le18$ and $k\ge r+2p$ (printed as $r+2m$), $(\mathbb E\|(GG^*)^{-1}\|^p)^{1/p}\le\frac{e^2(k+r)}{2(k-r)^2}$; the proof's condition (B.8) is $x=k-r\ge2p$.

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix
theorem inverse_wishart_spectral_moment {r k p : ℕ} (hp : 1 ≤ p) (hp18 : p ≤ 18)
    (hrk : r + 2 * p ≤ k) :
    Integrable (fun G : Fin r → Fin k → ℝ => specNorm (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ ^ p)
      (gaussianMatrix r k) ∧
    ∫ G, specNorm (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ ^ p ∂(gaussianMatrix r k)
      ≤ (Real.exp 1 ^ 2 * ((k : ℝ) + r) / (2 * ((k : ℝ) - r) ^ 2)) ^ p := by sorry
end GaussianMatrix
