-- Prove2me | Theorems.Thm_GaussianMatrix_gordon_lower
-- name    : GaussianMatrix.gordon_lower
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T07:22:00.740761+00:00
-- url     : https://prove2.me/theorems/b2d15044-bdd7-4d61-94cc-ecd86ef55aac
-- title:
--   Expected smallest singular value of a Gaussian matrix: $\mathbb E\,\sigma_{\min}(G)\ge\sqrt N-\sqrt n$
-- statement:
--   Let $n\ge 1$, let $G$ be an $N\times n$ random matrix with independent standard normal entries, and let
--   $$\sigma_{\min}(G)=\inf\{\|Gx\|_2:\ x\in\mathbb R^n,\ \|x\|_2=1\}$$
--   be its smallest singular value. Then
--   $$\sqrt N-\sqrt n\;\le\;\mathbb E\,\sigma_{\min}(G) .$$
--
--   This is the lower half of Gordon's theorem for Gaussian matrices. It is proved via Gordon's minimax comparison inequality: one compares $\min_u\max_v\langle Gu,v\rangle$ with $\min_u\max_v(\langle g,u\rangle+\langle h,v\rangle)$, and then uses $\mathbb E\|g_N\|-\mathbb E\|g_n\|\ge\sqrt N-\sqrt n$ for standard Gaussian vectors. Together with Gaussian concentration it yields $\mathbb P\{\sigma_{\min}(G)\le\sqrt N-\sqrt n-t\}\le e^{-t^2/2}$.
--
--   **Formalization Note.** `sMin` is the infimum of $\sqrt{(Ax)\cdot(Ax)}$ over the subtype $\{x\mid x\cdot x=1\}$. The hypothesis $n\ge1$ is necessary: for $n=0$ that set is empty, so `sMin` $=0$ while $\sqrt N>0$. When $N<n$ the inequality is trivial, since $\sigma_{\min}\ge 0$. The integrand is integrable ($1$-Lipschitz for the Frobenius norm).
-- source:
--   R. Vershynin, 'Introduction to the non-asymptotic analysis of random matrices' (2012), Theorem 5.32 (lower bound, via Gordon's inequality); Y. Gordon, 'Some inequalities for Gaussian processes and applications', Israel J. Math. 50 (1985), 265–289; K. R. Davidson and S. J. Szarek (2001), Theorem II.13. Theorem numbers from memory.

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

theorem gordon_lower {N n : ℕ} (hn : 1 ≤ n) :
    Real.sqrt N - Real.sqrt n ≤ ∫ A, sMin (Matrix.of A) ∂(gaussianMatrix N n) := by sorry

end GaussianMatrix
