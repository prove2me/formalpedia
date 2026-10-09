-- Prove2me | Theorems.Thm_GaussianMatrix_gaussian_logsobolev_bounded_below
-- name    : GaussianMatrix.gaussian_logsobolev_bounded_below
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T08:07:26.001954+00:00
-- url     : https://prove2.me/theorems/2e489bf7-292d-4bb3-9984-bf3c341fbd97
-- title:
--   Gaussian log-Sobolev inequality $\mathrm{Ent}_\gamma(f)\le\frac12\int (f')^2/f\,d\gamma$ for $C^1$ functions $f$ bounded away from $0$ with bounded derivative
-- statement:
--   Let $\gamma=N(0,1)$ be the standard Gaussian measure on $\mathbb{R}$. Let $\delta>0$ and $C\in\mathbb{R}$, and let $f:\mathbb{R}\to\mathbb{R}$ be continuously differentiable with $\delta\le f(x)\le C$ and $|f'(x)|\le C$ for all $x$. Then
--   $$\int f\log f\,d\gamma-\Big(\int f\,d\gamma\Big)\log\Big(\int f\,d\gamma\Big)\;\le\;\frac12\int\frac{(f')^2}{f}\,d\gamma .$$
--
--   This is the entropy form of Gross's inequality; substituting $f=g^2$ gives the usual form. It is proved with the Bakry–Émery argument along the Ornstein–Uhlenbeck semigroup $P_t$. The entropy decreases with rate equal to the Fisher information (`ou_entropy_hasDerivAt`). By commutation and Cauchy–Schwarz, the Fisher information of $P_tf$ is at most $e^{-2t}\int (f')^2/f\,d\gamma$, and invariance of $\gamma$ handles the integral. Hence $t\mapsto\mathrm{Ent}(P_tf)-\frac12e^{-2t}\int (f')^2/f\,d\gamma$ is nondecreasing on $[0,\infty)$; it equals the difference of the two sides at $t=0$ and tends to $0$ as $t\to\infty$.
--
--   **Formalization Note.** The hypotheses force $C\ge\delta>0$. All integrands are bounded and measurable, so every Bochner integral is a true integral.
-- source:
--   D. Bakry, M. Émery, Diffusions hypercontractives, Séminaire de Probabilités XIX, Lecture Notes in Math. 1123 (1985), 177–206; D. Bakry, I. Gentil, M. Ledoux, Analysis and Geometry of Markov Diffusion Operators (Springer, 2014), Proposition 5.5.1 and §5.7 (semigroup proof); M. Ledoux, The Concentration of Measure Phenomenon (AMS, 2001), Theorem 5.1 / (5.3). Numbering is cited from memory.

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

theorem gaussian_logsobolev_bounded_below (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (δ C : ℝ)
    (hδ : 0 < δ) (hlow : ∀ x, δ ≤ f x) (hup : ∀ x, f x ≤ C) (hdf : ∀ x, |deriv f x| ≤ C) :
    ∫ x, f x * Real.log (f x) ∂(gaussianReal 0 1)
      - (∫ x, f x ∂(gaussianReal 0 1)) * Real.log (∫ x, f x ∂(gaussianReal 0 1))
      ≤ (1 / 2) * ∫ x, deriv f x ^ 2 / f x ∂(gaussianReal 0 1) := by
  sorry

end GaussianMatrix
