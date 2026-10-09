-- Prove2me | Theorems.Thm_GaussianMatrix_gordon
-- name    : GaussianMatrix.gordon
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T02:47:32.327725+00:00
-- url     : https://prove2.me/theorems/5558fe10-2d53-4ac0-ae54-f141283965b5
-- title:
--   Gordon's theorem for Gaussian matrices: $\sqrt N-\sqrt n\le\mathbb E\,s_{\min}(A)\le\mathbb E\,s_{\max}(A)\le\sqrt N+\sqrt n$
-- statement:
--   Let $A\in\mathbb R^{N\times n}$, $n\ge1$, be a matrix whose entries are independent standard normal random variables, with extreme singular values
--   $$s_{\min}(A)=\inf_{\|x\|_2=1}\|Ax\|_2,\qquad s_{\max}(A)=\sup_{\|x\|_2=1}\|Ax\|_2=\|A\|.$$
--   Then $s_{\min}(A)$ and $s_{\max}(A)$ are integrable and
--   $$\sqrt N-\sqrt n\ \le\ \mathbb E\,s_{\min}(A)\ \le\ \mathbb E\,s_{\max}(A)\ \le\ \sqrt N+\sqrt n .$$
--
--   This is the exact non-asymptotic counterpart of the Bai–Yin law for Gaussian matrices (Gordon; Davidson–Szarek). The upper bound is proved from Slepian's comparison inequality, the lower bound from Gordon's minimax comparison inequality for Gaussian processes. Together with Gaussian concentration it yields the deviation inequalities for $s_{\min}$ and $s_{\max}$, and the lower bound $\mathbb E\,\sigma_{\min}\ge\sqrt t-\sqrt k$ is the starting point of small-ball estimates for Gaussian sketches.
--
--   **Formalization Note.** $s_{\min}$ is the infimum over the unit sphere of $\mathbb R^n$ (the hypothesis $n\ge1$ makes the sphere nonempty); $N\ge n$ is not required — for $N<n$ one has $s_{\min}(A)=0$ and the lower bound is trivially true. $s_{\max}(A)$ is Mathlib's $\ell_2$ operator norm. The conclusion includes integrability of both functions, so that the integrals are genuine expectations.
-- source:
--   R. Vershynin, *Introduction to the non-asymptotic analysis of random matrices*, Chapter 5 of Compressed Sensing: Theory and Applications (Y. Eldar, G. Kutyniok, eds.), Cambridge University Press, 2012, https://arxiv.org/abs/1011.3027 (v7), §5.3.1 p. 20–21, Theorem 5.32 (Gordon's theorem for Gaussian matrices): for an $N\times n$ matrix with independent standard normal entries, $\sqrt N-\sqrt n\le\mathbb E s_{\min}(A)\le\mathbb E s_{\max}(A)\le\sqrt N+\sqrt n$.

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix
theorem gordon {N n : ℕ} (hn : 1 ≤ n) :
    Integrable (fun A : Fin N → Fin n → ℝ => sMin (Matrix.of A)) (gaussianMatrix N n) ∧
    Integrable (fun A : Fin N → Fin n → ℝ => specNorm (Matrix.of A)) (gaussianMatrix N n) ∧
    Real.sqrt N - Real.sqrt n ≤ ∫ A, sMin (Matrix.of A) ∂(gaussianMatrix N n) ∧
    ∫ A, sMin (Matrix.of A) ∂(gaussianMatrix N n)
      ≤ ∫ A, specNorm (Matrix.of A) ∂(gaussianMatrix N n) ∧
    ∫ A, specNorm (Matrix.of A) ∂(gaussianMatrix N n) ≤ Real.sqrt N + Real.sqrt n := by sorry
end GaussianMatrix
