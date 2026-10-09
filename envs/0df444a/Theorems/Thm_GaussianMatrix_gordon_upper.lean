-- Prove2me | Theorems.Thm_GaussianMatrix_gordon_upper
-- name    : GaussianMatrix.gordon_upper
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T07:21:23.041853+00:00
-- url     : https://prove2.me/theorems/ce0cd846-82f6-4d12-acbc-07a022d60aa1
-- title:
--   Expected spectral norm of a Gaussian matrix: $\mathbb E\|G\|\le\sqrt N+\sqrt n$
-- statement:
--   Let $G$ be an $N\times n$ random matrix with independent standard normal entries, and let $\|G\|=\max_{\|x\|_2=1}\|Gx\|_2$ be its spectral norm (largest singular value). Then
--   $$\mathbb E\,\|G\|\;\le\;\sqrt N+\sqrt n .$$
--
--   This is the upper half of Gordon's theorem for Gaussian matrices. It is the input for the deviation bound $\mathbb P\{\|G\|\ge\sqrt N+\sqrt n+t\}\le e^{-t^2/2}$, and for the upper half of the conjunction `gordon`. It follows from the Sudakov–Fernique inequality by comparing $\langle Gu,v\rangle$ with $\langle g,u\rangle+\langle h,v\rangle$ on finite nets of the unit spheres.
--
--   **Formalization Note.** The law of $G$ is `gaussianMatrix N n`, and `specNorm` is Mathlib's $\ell_2\to\ell_2$ operator norm. No hypothesis on $N,n$ is needed: for $N=0$ or $n=0$ the norm is identically $0$. The integrand is integrable (it is $1$-Lipschitz for the Frobenius norm), so the Bochner-integral convention for non-integrable functions plays no role.
-- source:
--   R. Vershynin, 'Introduction to the non-asymptotic analysis of random matrices' (2012, in Compressed Sensing: Theory and Applications), Theorem 5.32 (upper bound), proof via Slepian/Sudakov–Fernique; K. R. Davidson and S. J. Szarek, 'Local operator theory, random matrices and Banach spaces', Handbook of the Geometry of Banach Spaces I (2001), Theorem II.13; R. Vershynin, High-Dimensional Probability (2018), Theorem 7.3.1. Theorem numbers from memory.

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

theorem gordon_upper {N n : ℕ} :
    ∫ A, specNorm (Matrix.of A) ∂(gaussianMatrix N n) ≤ Real.sqrt N + Real.sqrt n := by sorry

end GaussianMatrix
