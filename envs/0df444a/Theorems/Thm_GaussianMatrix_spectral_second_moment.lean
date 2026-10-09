-- Prove2me | Theorems.Thm_GaussianMatrix_spectral_second_moment
-- name    : GaussianMatrix.spectral_second_moment
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T02:47:09.006531+00:00
-- url     : https://prove2.me/theorems/e549105a-1161-4e4e-8c01-d2df2995c2b5
-- title:
--   Tropp–Webber spectral second moment: $(\mathbb E\|S\Gamma T\|^2)^{1/2}\le\|S\|\|T\|_F+\|S\|_F\|T\|$
-- statement:
--   Fix matrices $S\in\mathbb R^{a\times p}$ and $T\in\mathbb R^{m\times n}$ and let $\Gamma\in\mathbb R^{p\times m}$ be a standard Gaussian matrix. Then $\|S\Gamma T\|^2$ is integrable and
--   $$\bigl(\mathbb E\,\|S\,\Gamma\,T\|^2\bigr)^{1/2}\ \le\ \|S\|\,\|T\|_F+\|S\|_F\,\|T\| ,$$
--   where $\|\cdot\|$ is the spectral norm and $\|\cdot\|_F$ the Frobenius norm.
--
--   This is the second-moment version of the Gordon–Chevet bound (Tropp–Webber Lemma B.1); it is the form needed when spectral-norm errors are analyzed in mean square, e.g. for the core-noise and range-residual terms of truncated sketching algorithms, where it is combined with the inverse moments $\mathbb E\|G^{\dagger}\|^2$ and $\mathbb E\|G^{\dagger}\|_F^2$.
--
--   **Formalization Note.** The bound is stated in the equivalent squared form $\mathbb E\|S\Gamma T\|^2\le(\|S\|\|T\|_F+\|S\|_F\|T\|)^2$, together with integrability of the integrand.
-- source:
--   J. A. Tropp, R. J. Webber, *Randomized algorithms for low-rank matrix approximation: design, analysis, and applications*, 2023, https://arxiv.org/abs/2306.12418 (v1), Appendix B p. 47, Lemma B.1 (Moment bounds), first upper bound: $(\mathbb E\|SGT\|^2)^{1/2}\le\|S\|\|T\|_F+\|T\|\|S\|_F$.

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix
theorem spectral_second_moment {a p m n : ℕ} (S : Matrix (Fin a) (Fin p) ℝ)
    (T : Matrix (Fin m) (Fin n) ℝ) :
    Integrable (fun G : Fin p → Fin m → ℝ => specNorm (S * Matrix.of G * T) ^ 2) (gaussianMatrix p m) ∧
    ∫ G, specNorm (S * Matrix.of G * T) ^ 2 ∂(gaussianMatrix p m)
      ≤ (specNorm S * frobNorm T + frobNorm S * specNorm T) ^ 2 := by sorry
end GaussianMatrix
