-- Prove2me | Theorems.Thm_GaussianMatrix_expectation_norm_gaussian_diff
-- name    : GaussianMatrix.expectation_norm_gaussian_diff
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T07:39:34.663188+00:00
-- url     : https://prove2.me/theorems/07102780-7a56-4075-a370-2c3abb0ce479
-- title:
--   Norms of Gaussian vectors: $\mathbb E\|h_N\|_2-\mathbb E\|g_n\|_2\ge\sqrt N-\sqrt n$ for $1\le n\le N$
-- statement:
--   Let $1\le n\le N$ be integers. Let $h$ be a standard Gaussian vector in $\mathbb R^N$ and $g$ a standard Gaussian vector in $\mathbb R^n$, each with independent $N(0,1)$ coordinates, and let $\|\cdot\|_2$ be the Euclidean norm. Then
--   $$\sqrt N-\sqrt n\;\le\;\mathbb E\,\|h\|_2-\mathbb E\,\|g\|_2 .$$
--   Equivalently, $m\mapsto \mathbb E\|g_m\|_2-\sqrt m$ is nondecreasing on $m\ge1$, where $g_m$ is standard Gaussian in $\mathbb R^m$.
--
--   This is the elementary input that turns Gordon's bound $\mathbb E\,\sigma_{\min}(G)\ge\mathbb E\|h_N\|_2-\mathbb E\|g_n\|_2$ into the familiar $\mathbb E\,\sigma_{\min}(G)\ge\sqrt N-\sqrt n$. Note that $\mathbb E\|h_N\|_2\le\sqrt N$, so the inequality is not a consequence of Jensen's inequality. It is sharp to second order: with $a_m=\mathbb E\|g_m\|_2$, the gap $(a_{m+1}-a_m)-(\sqrt{m+1}-\sqrt m)$ is of order $m^{-3/2}/8$. One proof uses $a_m=\sqrt2\,\Gamma(\tfrac{m+1}2)/\Gamma(\tfrac m2)$, hence $a_m a_{m+1}=m$, together with log-convexity of $\Gamma$ and a monotone-ratio argument that yields $a_m^2\le m-\tfrac12+\tfrac{3}{20m}$.
--
--   **Formalization Note.** The law of $h$ is `Measure.pi fun _ : Fin N => gaussianReal 0 1`, and $\|x\|_2$ is written $\sqrt{\sum_i x_i^2}$. The hypothesis $n\ge1$ is necessary: for $n=0$ the claim would read $\sqrt N\le\mathbb E\|h_N\|_2$, which is false for every $N\ge1$ (e.g. $\mathbb E\|h_1\|=\sqrt{2/\pi}<1$). The hypothesis $n\le N$ is also needed, since the inequality reverses for $N<n$. Both integrands are integrable.
-- source:
--   R. Vershynin, High-Dimensional Probability (Cambridge Univ. Press, 2018), hint to Exercise 7.3.4 (p. 170): 'f(n) := E||g||_2 - sqrt(n) is increasing in dimension n (take this fact for granted; it can be proved by a tedious calculation)'. Used in K. R. Davidson and S. J. Szarek, 'Local operator theory, random matrices and Banach spaces', Handbook of the Geometry of Banach Spaces I (2001), proof of Theorem II.13 (theorem number from memory).

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

theorem expectation_norm_gaussian_diff {N n : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) :
    Real.sqrt N - Real.sqrt n ≤
      ∫ x, Real.sqrt (∑ i, x i ^ 2) ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1)
        - ∫ x, Real.sqrt (∑ i, x i ^ 2) ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) := by sorry

end GaussianMatrix
