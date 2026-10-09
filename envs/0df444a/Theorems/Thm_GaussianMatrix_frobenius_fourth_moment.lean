-- Prove2me | Theorems.Thm_GaussianMatrix_frobenius_fourth_moment
-- name    : GaussianMatrix.frobenius_fourth_moment
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T02:36:08.786721+00:00
-- url     : https://prove2.me/theorems/9ef9dc47-b920-443a-9e87-a69f608c40cf
-- title:
--   Fourth Frobenius moment of a scaled Gaussian matrix: $\mathbb E\|S\Gamma T\|_F^4=(\|S\|_F^2\|T\|_F^2)^2+2\|S^{\mathsf T}S\|_F^2\|TT^{\mathsf T}\|_F^2$
-- statement:
--   Fix matrices $S\in\mathbb R^{a\times p}$ and $T\in\mathbb R^{m\times n}$ and let $\Gamma\in\mathbb R^{p\times m}$ be a standard Gaussian matrix. Then
--   $$\mathbb E\,\|S\,\Gamma\,T\|_F^4=\bigl(\|S\|_F^2\,\|T\|_F^2\bigr)^2+2\,\|S^{\mathsf T}S\|_F^2\,\|TT^{\mathsf T}\|_F^2 .$$
--
--   Since $\|S\Gamma T\|_F^2=\operatorname{tr}(\Gamma^{\mathsf T}S^{\mathsf T}S\,\Gamma\,TT^{\mathsf T})$ is a quadratic form $\gamma^{\mathsf T}(S^{\mathsf T}S\otimes TT^{\mathsf T})\gamma$ in the Gaussian vector $\gamma=\operatorname{vec}\Gamma$, this is the classical formula $\mathbb E(\gamma^{\mathsf T}C\gamma)^2=(\operatorname{tr}C)^2+2\operatorname{tr}(C^2)$ for a symmetric $C$ (Isserlis' theorem), with $\operatorname{tr}(C^2)=\|S^{\mathsf T}S\|_F^2\|TT^{\mathsf T}\|_F^2$. The special case $S=I_k$, $T=I_t$ is the chi-square moment $\mathbb E\|\Omega_1\|_F^4=(kt)^2+2kt$ used in the analysis of early-truncated sketching, and the identity controls the variance of $\|S\Gamma T\|_F^2$ since $\operatorname{Var}\|S\Gamma T\|_F^2=2\|S^{\mathsf T}S\|_F^2\|TT^{\mathsf T}\|_F^2$.
--
--   **Formalization Note.** The expectation is a Lebesgue integral against $\gamma_{p,m}$ of a polynomial in the entries of $\Gamma$.
-- source:
--   Isserlis' theorem (L. Isserlis, *On a formula for the product-moment coefficient of any order of a normal frequency distribution in any number of variables*, Biometrika 12(1–2), 134–139, 1918, https://doi.org/10.1093/biomet/12.1-2.134) applied to the Gaussian quadratic form $\operatorname{tr}(\Gamma^{\mathsf T}S^{\mathsf T}S\Gamma TT^{\mathsf T})$: $\mathbb E(\gamma^{\mathsf T}C\gamma)^2=(\operatorname{tr}C)^2+2\operatorname{tr}C^2$ for symmetric $C=S^{\mathsf T}S\otimes TT^{\mathsf T}$ and standard Gaussian $\gamma=\operatorname{vec}\Gamma$. The special case $S=I_p$, $T=I_m$ is the chi-square moment $\mathbb E(\chi^2_{pm})^2=(pm)^2+2pm$, i.e. N. Halko, P.-G. Martinsson, J. A. Tropp, *Finding structure with randomness: probabilistic algorithms for constructing approximate matrix decompositions*, SIAM Review 53(2), 2011, https://arxiv.org/abs/0909.4061 (v2), Appendix A.3.1 p. 65, Proposition A.8 with $q=2$ ($\mathbb E\,\Xi^q=2^q\Gamma(k/2+q)/\Gamma(k/2)$). Compare J. A. Tropp, R. J. Webber, *Randomized algorithms for low-rank matrix approximation: design, analysis, and applications*, 2023, https://arxiv.org/abs/2306.12418 (v1), Appendix B p. 47, Lemma B.1 (Schatten-4 version).

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix
theorem frobenius_fourth_moment {a p m n : ℕ} (S : Matrix (Fin a) (Fin p) ℝ)
    (T : Matrix (Fin m) (Fin n) ℝ) :
    ∫ G, frobSq (S * Matrix.of G * T) ^ 2 ∂(gaussianMatrix p m)
      = (frobSq S * frobSq T) ^ 2 + 2 * frobSq (Sᵀ * S) * frobSq (T * Tᵀ) := by sorry
end GaussianMatrix
