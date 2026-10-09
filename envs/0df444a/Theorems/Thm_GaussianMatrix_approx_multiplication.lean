-- Prove2me | Theorems.Thm_GaussianMatrix_approx_multiplication
-- name    : GaussianMatrix.approx_multiplication
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T02:37:21.810798+00:00
-- url     : https://prove2.me/theorems/45f1ef39-cd6a-4ad0-949f-c9233f0545f0
-- title:
--   Gaussian approximate matrix multiplication: $\mathbb E\|MSS^{\mathsf T}N^{\mathsf T}-MN^{\mathsf T}\|_F^2=(\|M\|_F^2\|N\|_F^2+\|MN^{\mathsf T}\|_F^2)/t$
-- statement:
--   Fix matrices $M\in\mathbb R^{a\times n}$ and $N\in\mathbb R^{b\times n}$, let $t\ge1$, and let $S\in\mathbb R^{n\times t}$ have independent $\mathcal N(0,1/t)$ entries, i.e. $S=t^{-1/2}\Omega$ with $\Omega\sim\gamma_{n,t}$ standard Gaussian. Then
--   $$\mathbb E\,\bigl\|M S S^{\mathsf T}N^{\mathsf T}-MN^{\mathsf T}\bigr\|_F^2=\frac{\|M\|_F^2\|N\|_F^2+\|MN^{\mathsf T}\|_F^2}{t}\ \le\ \frac{2}{t}\,\|M\|_F^2\|N\|_F^2 .$$
--
--   The random product $MSS^{\mathsf T}N^{\mathsf T}$ is the sketched (Monte Carlo) estimate of $MN^{\mathsf T}$ obtained from $t$ Gaussian test vectors; the identity gives its exact mean-squared error, decaying like $1/t$. It is the second-moment input for one-pass low-rank approximation algorithms, where it controls the term $\|A_2SS^{\mathsf T}A_2^{\mathsf T}-A_2A_2^{\mathsf T}\|_F$ with $M=N=A_2$.
--
--   **Formalization Note.** $SS^{\mathsf T}$ is written as $\tfrac1t\,\Omega\Omega^{\mathsf T}$ with $\Omega$ standard Gaussian, so the hypothesis is exactly that the entries of $S$ are $\mathcal N(0,1/t)$. The statement is the conjunction of the identity and the stated upper bound; the latter is the elementary inequality $\|MN^{\mathsf T}\|_F\le\|M\|_F\|N\|_F$.
-- source:
--   Direct second-moment computation from Isserlis' theorem (L. Isserlis, *On a formula for the product-moment coefficient of any order of a normal frequency distribution in any number of variables*, Biometrika 12(1–2), 134–139, 1918, https://doi.org/10.1093/biomet/12.1-2.134): writing the columns of $S$ as $g_\ell/\sqrt t$ with independent standard Gaussian vectors $g_\ell$, the $(i,j)$ entry of $MSS^{\mathsf T}N^{\mathsf T}-MN^{\mathsf T}$ is $\frac1t\sum_\ell\bigl((m_i^{\mathsf T}g_\ell)(g_\ell^{\mathsf T}n_j)-m_i^{\mathsf T}n_j\bigr)$, which has mean $0$ and variance $\frac1t(\|m_i\|^2\|n_j\|^2+(m_i^{\mathsf T}n_j)^2)$ by Isserlis' pairing formula $\mathbb E[g_ag_bg_cg_d]=\delta_{ab}\delta_{cd}+\delta_{ac}\delta_{bd}+\delta_{ad}\delta_{bc}$; summing over $i,j$ gives the identity. The inequality is $\|MN^{\mathsf T}\|_F\le\|M\|_F\|N\|_F$. This is the exact Gaussian case of the approximate-matrix-multiplication (sketched product) second-moment bound; cf. N. Halko, P.-G. Martinsson, J. A. Tropp, *Finding structure with randomness: probabilistic algorithms for constructing approximate matrix decompositions*, SIAM Review 53(2), 2011, https://arxiv.org/abs/0909.4061 (v2), §10.1 p. 55, Proposition 10.1 for the companion identity $\mathbb E\|SGT\|_F^2=\|S\|_F^2\|T\|_F^2$.

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix
theorem approx_multiplication {a b n t : ℕ} (ht : 1 ≤ t) (M : Matrix (Fin a) (Fin n) ℝ)
    (N : Matrix (Fin b) (Fin n) ℝ) :
    ∫ Ω, frobSq (M * ((1 / (t : ℝ)) • (Matrix.of Ω * (Matrix.of Ω)ᵀ)) * Nᵀ - M * Nᵀ)
        ∂(gaussianMatrix n t)
      = (frobSq M * frobSq N + frobSq (M * Nᵀ)) / t ∧
    (frobSq M * frobSq N + frobSq (M * Nᵀ)) / t ≤ 2 / t * (frobSq M * frobSq N) := by sorry
end GaussianMatrix
