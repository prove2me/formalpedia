-- Prove2me | Theorems.Thm_GaussianMatrix_extreme_singular_values_deviation
-- name    : GaussianMatrix.extreme_singular_values_deviation
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T02:49:07.876214+00:00
-- url     : https://prove2.me/theorems/88fc7d4c-7b8e-42f2-9db8-21f319d608d7
-- title:
--   Deviation of the extreme singular values of a Gaussian matrix: $\sqrt N-\sqrt n-t\le s_{\min}(A)\le s_{\max}(A)\le\sqrt N+\sqrt n+t$ with probability $\ge1-2e^{-t^2/2}$
-- statement:
--   Let $A\in\mathbb R^{N\times n}$, $n\ge1$, be a matrix whose entries are independent standard normal random variables. Then for every $t\ge0$, with probability at least $1-2\exp(-t^2/2)$,
--   $$\sqrt N-\sqrt n-t\ \le\ s_{\min}(A)\qquad\text{and}\qquad s_{\max}(A)\ \le\ \sqrt N+\sqrt n+t ,$$
--   where $s_{\min}(A)=\inf_{\|x\|_2=1}\|Ax\|_2$ and $s_{\max}(A)=\|A\|$ is the spectral norm.
--
--   This is Vershynin's Corollary 5.35, the non-asymptotic Gaussian analogue of the Bai–Yin law with explicit sub-Gaussian deviations. It follows from Gordon's expectation bounds and Gaussian concentration, since $s_{\min}$ and $s_{\max}$ are $1$-Lipschitz functions of the matrix in the Frobenius norm. It is the standard tool for showing that a Gaussian sketch is a near-isometry, and for lower-bounding $\sigma_{\min}$ of the head block $\Omega_1$ in randomized low-rank approximation.
--
--   **Formalization Note.** The probability is a measure in $[0,\infty]$ and the lower bound $1-2e^{-t^2/2}$ is computed with truncated subtraction, so the statement is vacuous when $2e^{-t^2/2}\ge1$, i.e. $t\le\sqrt{2\log2}$, exactly as in the source. The inequality $s_{\min}(A)\le s_{\max}(A)$ is not part of the event (it is immediate).
-- source:
--   R. Vershynin, *Introduction to the non-asymptotic analysis of random matrices*, Chapter 5 of Compressed Sensing: Theory and Applications (Y. Eldar, G. Kutyniok, eds.), Cambridge University Press, 2012, https://arxiv.org/abs/1011.3027 (v7), §5.3.1 p. 21, Corollary 5.35 (Gaussian matrices, deviation): for every $t\ge0$, with probability at least $1-2\exp(-t^2/2)$, $\sqrt N-\sqrt n-t\le s_{\min}(A)\le s_{\max}(A)\le\sqrt N+\sqrt n+t$.

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix
theorem extreme_singular_values_deviation {N n : ℕ} (hn : 1 ≤ n) (t : ℝ) (ht : 0 ≤ t) :
    1 - ENNReal.ofReal (2 * Real.exp (-t ^ 2 / 2))
      ≤ (gaussianMatrix N n) {A | Real.sqrt N - Real.sqrt n - t ≤ sMin (Matrix.of A) ∧
          specNorm (Matrix.of A) ≤ Real.sqrt N + Real.sqrt n + t} := by sorry
end GaussianMatrix
