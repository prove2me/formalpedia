-- Prove2me | Theorems.Thm_GaussianMatrix_spectral_second_moment_bound
-- name    : GaussianMatrix.spectral_second_moment_bound
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T07:23:06.692413+00:00
-- url     : https://prove2.me/theorems/498cd9d3-107e-4b4d-a90b-f686d78b5ad1
-- title:
--   Second-moment Chevet bound: $\mathbb E\|SGT\|^2\le(\|S\|\|T\|_F+\|S\|_F\|T\|)^2$
-- statement:
--   Let $S\in\mathbb R^{a\times p}$ and $T\in\mathbb R^{m\times n}$ be fixed matrices, and let $G$ be a $p\times m$ random matrix with independent standard normal entries. Write $\|\cdot\|$ for the spectral norm and $\|\cdot\|_F$ for the Frobenius norm. Then
--   $$\mathbb E\,\|SGT\|^2\;\le\;\big(\|S\|\,\|T\|_F+\|S\|_F\,\|T\|\big)^2 .$$
--
--   This strengthens the first-moment Chevet–Gordon bound: by Cauchy–Schwarz it implies $\mathbb E\|SGT\|\le\|S\|\|T\|_F+\|S\|_F\|T\|$. It is used in the mean-square error analysis of the randomized SVD. It does **not** follow from the first-moment bound combined with Gaussian concentration: that route only gives $(\|S\|\|T\|_F+\|S\|_F\|T\|)^2+\|S\|^2\|T\|^2$.
--
--   **Formalization Note.** The integrand $\|S\,\mathrm{of}(G)\,T\|^2$ is integrable, since it is the square of a Lipschitz function of a Gaussian matrix, so the Bochner-integral convention plays no role. All dimensions may be zero.
-- source:
--   J. A. Tropp and R. J. Webber, 'Randomized algorithms for low-rank matrix approximation: Design, analysis, and applications', arXiv:2306.12418 (2023), Lemma B.1 (first upper bound; proof in Appendix B, p. 47) — lemma number as cited in the task; obtained there by a Gaussian comparison argument.

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

theorem spectral_second_moment_bound {a p m n : ℕ} (S : Matrix (Fin a) (Fin p) ℝ)
    (T : Matrix (Fin m) (Fin n) ℝ) :
    ∫ G, specNorm (S * Matrix.of G * T) ^ 2 ∂(gaussianMatrix p m)
      ≤ (specNorm S * frobNorm T + frobNorm S * specNorm T) ^ 2 := by sorry

end GaussianMatrix
