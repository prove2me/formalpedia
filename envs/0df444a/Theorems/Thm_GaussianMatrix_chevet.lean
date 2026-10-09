-- Prove2me | Theorems.Thm_GaussianMatrix_chevet
-- name    : GaussianMatrix.chevet
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T02:46:26.20186+00:00
-- url     : https://prove2.me/theorems/852974f2-721c-49f3-9a9f-e857d47776d4
-- title:
--   Gordon–Chevet bound on the expected spectral norm of a scaled Gaussian matrix: $\mathbb E\|S\Gamma T\|\le\|S\|\|T\|_F+\|S\|_F\|T\|$
-- statement:
--   Fix matrices $S\in\mathbb R^{a\times p}$ and $T\in\mathbb R^{m\times n}$ and let $\Gamma\in\mathbb R^{p\times m}$ be a standard Gaussian matrix. Then $\|S\Gamma T\|$ is integrable and
--   $$\mathbb E\,\|S\,\Gamma\,T\|\ \le\ \|S\|\,\|T\|_F+\|S\|_F\,\|T\|,$$
--   where $\|\cdot\|$ is the spectral norm and $\|\cdot\|_F$ the Frobenius norm.
--
--   This is the expected spectral norm bound of Halko–Martinsson–Tropp Proposition 10.1 (eq. (10.2)) and Appendix A, Proposition A.2, due to Gordon and proved from a sharp form of Slepian's lemma (Chevet's inequality). With $S=I$, $T=I$ it recovers $\mathbb E\|\Gamma\|\le\sqrt p+\sqrt m$; in the randomized SVD it bounds $\mathbb E\|\Sigma_2\Omega_2\Omega_1^{\dagger}\|$ conditionally on $\Omega_1$.
--
--   **Formalization Note.** The conclusion is the conjunction of integrability (so the integral is a genuine expectation) and the bound.
-- source:
--   N. Halko, P.-G. Martinsson, J. A. Tropp, *Finding structure with randomness: probabilistic algorithms for constructing approximate matrix decompositions*, SIAM Review 53(2), 2011, https://arxiv.org/abs/0909.4061 (v2), §10.1 p. 55, Proposition 10.1 eq. (10.2), and Appendix A.1 p. 64, Proposition A.2: $\mathbb E\|SGT\|\le\|S\|\|T\|_F+\|S\|_F\|T\|$.

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix
theorem chevet {a p m n : ℕ} (S : Matrix (Fin a) (Fin p) ℝ) (T : Matrix (Fin m) (Fin n) ℝ) :
    Integrable (fun G : Fin p → Fin m → ℝ => specNorm (S * Matrix.of G * T)) (gaussianMatrix p m) ∧
    ∫ G, specNorm (S * Matrix.of G * T) ∂(gaussianMatrix p m)
      ≤ specNorm S * frobNorm T + frobNorm S * specNorm T := by sorry
end GaussianMatrix
