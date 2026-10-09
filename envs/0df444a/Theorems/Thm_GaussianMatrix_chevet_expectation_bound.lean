-- Prove2me | Theorems.Thm_GaussianMatrix_chevet_expectation_bound
-- name    : GaussianMatrix.chevet_expectation_bound
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T07:22:31.315475+00:00
-- url     : https://prove2.me/theorems/d7615cc3-aa10-4707-9ca5-dca4c3e05264
-- title:
--   Chevet–Gordon bound: $\mathbb E\|SGT\|\le\|S\|\|T\|_F+\|S\|_F\|T\|$ for a standard Gaussian matrix $G$
-- statement:
--   Let $S\in\mathbb R^{a\times p}$ and $T\in\mathbb R^{m\times n}$ be fixed matrices, and let $G$ be a $p\times m$ random matrix with independent standard normal entries. Write $\|\cdot\|$ for the spectral norm and $\|\cdot\|_F$ for the Frobenius norm. Then
--   $$\mathbb E\,\|SGT\|\;\le\;\|S\|\,\|T\|_F+\|S\|_F\,\|T\| .$$
--
--   This sharp-constant form of Chevet's inequality is used in the analysis of randomized range finders (randomized SVD), where it controls the error term $\|\Sigma_2\Omega_2\Omega_1^\dagger\|$. Note that it does not follow from the Sudakov–Fernique inequality with the naive comparison process when the index sets are ellipsoids rather than spheres. It also follows from the second-moment bound `spectral_second_moment_bound` by Cauchy–Schwarz.
--
--   **Formalization Note.** The law of $G$ is `gaussianMatrix p m`, and the matrix is `S * Matrix.of G * T`. All dimensions may be zero. The integrand is integrable ($\|S\|\|T\|$-Lipschitz for the Frobenius norm).
-- source:
--   N. Halko, P.-G. Martinsson, J. A. Tropp, 'Finding structure with randomness', SIAM Review 53(2) (2011), Proposition 10.1 (numbering from memory), attributing the bound to Y. Gordon (Israel J. Math. 50 (1985); Israel J. Math. 64 (1988)); see also S. Chevet (1978) for the inequality with non-sharp form.

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

theorem chevet_expectation_bound {a p m n : ℕ} (S : Matrix (Fin a) (Fin p) ℝ)
    (T : Matrix (Fin m) (Fin n) ℝ) :
    ∫ G, specNorm (S * Matrix.of G * T) ∂(gaussianMatrix p m)
      ≤ specNorm S * frobNorm T + frobNorm S * specNorm T := by sorry

end GaussianMatrix
